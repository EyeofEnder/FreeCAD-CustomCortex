import FreeCAD as App
import FreeCADGui as GUI
import Draft
import Sketcher
import Part
import numpy as np
import scipy as sc
import scipy.optimize as opt
import math
import os
import statistics
import importlib
import freecad.Curves as curves_wb

def find_or_create(doc,label,objtype):
    
    # Searches for an object with label label if it exists in doc, otherwise creates and returns an object of type objtype and label label
    
    if not (found := doc.findObjects(Label=f"{label}$")):
    
        return doc.addObject(objtype,label)
        
    else:
    
        return found[0]
        
def get_label_numbers(label,strip="0"):
    
    return "".join([k if k.isdigit() else "" for k in label.lstrip("0")])
    
def convert_labels(labels):
    
    l = [int(get_label_numbers(lab)) for lab in labels]
    
    l.sort()
    
    return "".join([f"{lab}-" for lab in l]).rstrip("-")

def get_spline(sel,check_only=False,get_wire=False):
    
    
    #print(sel)

    while type(sel) != Part.BSplineCurve:
        
        if hasattr(sel,"Wires") and get_wire and sel.Wires:
            
            return sel.Wires[0]

        if hasattr(sel,"Shape"):

            sel = sel.Shape

        elif hasattr(sel,"Curve"):

            sel = sel.Curve
            
        elif hasattr(sel,"Edges"):

            if len(sel.Edges) == 1:

                sel = sel.Edges[0]
                
            else:
                
                print(f"Object {sel} has more than 1 edge or none.")
                
                sel = sel.Edges[0]
                
        else:
            
            if not check_only:
            
                raise Exception("Selected object has no Shape, Curve or BSplineCurve attribute")
                
            else:
                
                return False

    return sel if not get_wire else None

def get_splines(sel,check_only=False):
        
    splines = []
    
    valid = True
        
    for s in sel:
        
        c = get_spline(s)
        
        if not check_only:
            
            splines.append(c)
            
        elif not c:
            
            valid = False
           
    return splines
    
def get_constraint_by_name(sketch,name):
    
    return [c for c in sketch.Constraints if c.Name == name][0]

class node():
    
    def __init__(self,position,connection,intersection_point_obj,generation_parameters,angles):
        
        self.position = position # connected edges regardless of electrical connection
        self.connection = connection # electrical connections
        assert type(intersection_point_obj) == intersection_point
        self.intersection_point_obj = intersection_point_obj
        self.label = self.intersection_point_obj.point_id
        self.generation_parameters = generation_parameters
        self.angles = angles # angles in °, ccw from first listed curve
        
class curve():
    
    def __init__(self,curve_obj,label):
        
        assert type(curve_obj) in (Part.Feature,Part.Wire,Part.Edge)
        
        self.curve_obj = curve_obj
        self.label = label
        self.spline = get_spline(self.curve_obj)
        
        

class intersection_point():
    
    def __init__(self,curves,splines,parameters,centers,normals=[],distances=[],limits=[],angles=[],labels=[],tangents=[]):
        
        self.curves = curves
        self.splines = splines
        self.parameters = parameters
        self.centers = centers
        self.normals = normals
        self.distances = distances
        self.limits = limits
        self.angles = angles
        self.labels = labels
        self.tangents = tangents
        print(self.labels)
        self.point_id = convert_labels(self.labels)
        
        
    def get_angles(self,start_label):
    
        assert start_label in self.labels
    
        angles = {}
        
        for l in range(0,len(self.labels)):
            
            if self.labels[l] != start_label:
               
                angles[self.labels[l]] = round(math.acos(round(self.tangents[self.labels.index(start_label)].dot(self.tangents[l]),6))*180/math.pi,1)
        
        
        return angles
        
class curve_net():

    def __init__(self,selection=None,curves=[],nodes=[],sketches={"node_frame":None,"node_conductor":None,"frame":None,"frame_conductors":None},objects={"cutout":None},node_params=None,default_node_params=(-0.5,2,(10,-5,0),(10,-185,0)),center=App.Vector(0,0,0),object_offsets={"cutout":(0,0,-0.5)},piped_curves={}):
            
        self.sketches = sketches
        self.groups = {}
        self.objects = objects
        self.default_node_params = default_node_params # (z offset, z distance, (angle, angle offset, z offset), (angle1, angle offset1, z offset1) ...)
        self.node_params = node_params if node_params else default_node_params
        self.object_offsets = object_offsets
        self.selection = []
        self.piped_curves = piped_curves
        #self.points = points
        
        if selection:
            
            self.from_selection(selection,center=center)
            
        else: 
            
            self.curves = curves      
            self.nodes = nodes
        
        self.adjacency_matrix = np.ndarray(shape=(len(self.nodes),len(self.nodes)),dtype=bool)
        
    def from_selection(self,sel,center=App.Vector(0,0,0)):
        
        doc = App.activeDocument()
        
        gen = find_or_create(doc,"Generated","App::DocumentObjectGroup")
        
        self.selection = sel
        
        curves, merged_points = get_point_net(sel,merge=True)
        
        for p in merged_points.keys():
            
            if merged_points[p].normals[0].dot(merged_points[p].centers[0].sub(center)) < 0:
                
                merged_points[p].normals[0].multiply(-1)
        
        self.nodes = []
        
        for p in merged_points.keys():
            
            self.nodes.append(node(position=p,connection=p,intersection_point_obj = merged_points[p],generation_parameters=self.default_node_params,angles=merged_points[p].angles))
            
        for n in self.node_params.keys():
            
            for k in self.nodes:
                
                if k.label == n:
                
                    k.generation_parameters = self.node_params[n]
            
        self.curves = curves
        
        aux_curves_group,aux_curves = interpolate_aux_curves(curves=list(self.curves.values()),normal_points=[],mode="center",center=center,degree=5,curve_label="aux_curve",group_label="interpolated_aux_curves")
     
        self.groups["aux_curves"] = aux_curves_group
        
        gen.addObject(aux_curves_group)
        
        self.aux_curves = aux_curves
        
    def set_node_params(self,param_list):
        
        for n in range(0,len(self.nodes)):
            
            if n <= len(param_list):
                
                self.nodes[n].generation_parameters=param_list[n]
       
    def get_adjacency_matrix(self):
        
        self.point_indices = self.get_point_indices()
        
        m = np.zeros(shape=(len(self.point_indices),len(self.point_indices)))
        
        for i in range(0,len(self.point_indices)):
            
            for j in range(0,len(self.point_indices)):
                
                for k in self.points.keys():
                    
                    if k in ((i,j),(j,i)):
                        
                        m[i,j] = 1
                        
        return m
        
    def clear(self):
        
        doc = App.activeDocument()
        
        for k in self.groups.keys():
            
            doc.removeObject(k)
            
        for k in self.aux_curves:
            
            doc.removeObject(k)
        
    def generate(self):
        
        #autoconstruct(net,node_objects=[],pipes=[],aux_curves=[],tolerance=1,split=False,interpolate_normals=True,center=App.Vector(0,0,0),orientations={},node_group_names=[],pipe_group_names=[],pipe_body_names=[])
        
        doc = App.activeDocument()
        
        curves = list(self.curves.values())
        
        generated = find_or_create(doc,"Generated","App::DocumentObjectGroup")
        
        text = find_or_create(doc,"Labels","App::DocumentObjectGroup")
        
        angles_text = ""
        
        if self.sketches["node_frame"] and self.sketches["node_conductor"]:
                
            node_frame_group = find_or_create(doc,"generated_nodes_frames$","App::DocumentObjectGroup")
            
            node_conductor_group = find_or_create(doc,"generated_nodes_conductors$","App::DocumentObjectGroup")
                
            self.groups["nodes"] = [node_frame_group, node_conductor_group]
            
            for k in range(0, len(self.nodes)):
                
                print(f"Generation parameters of node {self.nodes[k].label}: ", self.nodes[k].generation_parameters)
                
                if len(self.nodes[k].generation_parameters) > 2:
                    
                    print("Angle params")
                
                    params = self.nodes[k].generation_parameters[2:]
                
                    angles = [a[0] for a in params]
                
                    angle_offsets = [a[1] for a in params]
                
                    z_offsets = [a[2] for a in params]
                    
                else:
                    
                    params,angles,angle_offsets,z_offsets = [],[],[],[]
                
                #raise Exception("Improvised breakpoint.")
                
                angles_text = angles_text + f"Node angles from {self.nodes[k].label}: {self.nodes[k].intersection_point_obj.get_angles(self.nodes[k].intersection_point_obj.labels[0])}\n"
                
                calc_angles = self.nodes[k].intersection_point_obj.get_angles(self.nodes[k].intersection_point_obj.labels[0])
                
                calc_angles[self.nodes[k].intersection_point_obj.labels[0]] = 0
                
                text_rot = App.Rotation(App.Vector(1,0,0),self.nodes[k].intersection_point_obj.tangents[0])
                
                text_placement = App.Placement()
                
                text_placement.Base = self.nodes[k].intersection_point_obj.centers[0] * 1.1
                
                text.addObject(text_obj:=Draft.make_text(placement=text_placement,string=[self.nodes[k].label,str(self.nodes[k].generation_parameters),str(calc_angles),str(self.nodes[k].intersection_point_obj.labels)]))
                
                text_obj.Visibility = False
                
                n_frame,n_cond = generate_layered_node(frame_xsection=self.sketches["node_frame"],conductor_xsections=[self.sketches["node_conductor"] for l in params],conductor_angles=angles,conductor_angle_offsets=angle_offsets,conductor_z_offsets=z_offsets,placement=self.nodes[k].intersection_point_obj, body_label="layered_node",z_offset=self.nodes[k].generation_parameters[0])
                
                node_conductor_group.addObject(n_cond)
                
                node_frame_group.addObject(n_frame)
                
            generated.addObject(node_conductor_group)
            
            generated.addObject(node_frame_group)
            
        print("Aux net:", self.aux_curves)
            
        if self.sketches["frame"]:
        
            piped = self.piped_curves["frame"] if "frame" in self.piped_curves.keys() else []
            
            frame = autopipe(curves,pipe_sketch=self.sketches["frame"],subtractive=False,group_label="Frame",body_label="pipe_frame",aux_net=self.aux_curves,piped=piped)[0]
            
            self.groups["frame"] = frame
            
            generated.addObject(frame)
            
        if self.sketches["frame_conductors"]:
            
            self.groups["frame_conductors"] = []
            
            for c in self.sketches["frame_conductors"]:
            
                piped = self.piped_curves[c.Label] if c.Label in self.piped_curves.keys() else []
                
                cond = autopipe(curves,pipe_sketch=c,subtractive=False,group_label="Conductors",body_label="pipe_conductor",aux_net=self.aux_curves,piped=piped)[0]
                
                self.groups["frame_conductors"].append(cond)
                
                generated.addObject(cond)
                
        if self.objects:
            
            self.groups["objects" ] = []
            
            for k in self.objects.keys():
                
                #points = [n.intersection_point_obj for n in self.nodes]
                
                merged_points = {p.position:p.intersection_point_obj for p in self.nodes}
                
                node_group,node_bodies = autonode(points=merged_points,node_object=self.objects[k],group_label=f"object_{k}",orientations={},offset=self.object_offsets[k])
                
                self.groups["objects"].append(node_bodies)
                
                generated.addObject(node_group)
                
        print(angles_text)
                
        for k in self.nodes:
            
            print(k.label)
                
        doc.recompute()

def debug_line(origin,direction,label="debug_line"):
    
    doc = App.activeDocument()
    
    res = App.Vector(origin).add(App.Vector(direction))
    
    wire = Draft.makeWire((App.Vector(origin),res))
    
    wire.Label = label
    
    return wire
    
def calculate_resistance(curve,profile,resistivity=(1,1,1)):
    
    pass
    
def reapproximate_curves(curves,point_count=10,group_label="approx_curves"):
    
    doc = App.activeDocument()
    
    group = find_or_create(doc,group_label,"App::DocumentObjectGroup")
    
    if str(type(curves[0])) == "<class 'Gui.SelectionObject'>":
        
        sel = curves[0]
        
        for sub in sel.SubElementNames:
            
            disc = doc.addObject("Part::FeaturePython",f"{sel.Object.Label}_discretization")
            
            curves_wb.Discretize.Discretization(obj=disc,edge=(sel.Object,sub))
                
            curves_wb.Discretize.ViewProviderDisc(disc.ViewObject)
            
            disc.ViewObject.PointSize = 3
            
            disc.Number = point_count
            
            disc.Visibility = False
            
            #group.addObject(disc)
        
            curves_wb.approximate.Approximate(reapprox:=doc.addObject("Part::FeaturePython",f"{sel.Object.Label}_approx"),disc)
                
            curves_wb.approximate.ViewProviderApp(reapprox.ViewObject)
            
            group.addObject(reapprox)
    
    else:
    
        for c in curves:
            
            disc = doc.addObject("Part::FeaturePython",f"{c.Label}_discretization")
            
            curves_wb.Discretize.Discretization(obj=disc,edge=(c,"Edge1"))
                
            curves_wb.Discretize.ViewProviderDisc(disc.ViewObject)
            
            disc.ViewObject.PointSize = 3
            
            disc.Number = point_count
            
            #group.addObject(disc)
        
            curves_wb.approximate.Approximate(reapprox:=doc.addObject("Part::FeaturePython",f"{c.Label}_approx"),disc)
                
            curves_wb.approximate.ViewProviderApp(reapprox.ViewObject)
            
            group.addObject(reapprox)
            
    doc.recompute()


def get_closest_point(w0,w1):
    
    c0,c1 = get_spline(w0),get_spline(w1)
    
    l0,l1 = get_label_numbers(w0.Label),get_label_numbers(w1.Label)
    
    w0,w1 = get_spline(w0,get_wire=True), get_spline(w1,get_wire=True)

    assert type(c0) == type(c1) == Part.BSplineCurve

    def get_distance(c0,c1,t0,t1):

        p0,p1 = c0.getD0(t0), c1.getD0(t1)

        dist = math.sqrt((p0.x-p1.x)**2 + (p0.y-p1.y)**2+(p0.z-p1.z)**2)

        return dist

    params = tuple(opt.minimize(lambda x: get_distance(c0=c0,c1=c1,t0=x[0],t1=x[1]),x0=[0.5,0.5],bounds=((0,1),(0,1))).x)
    
    distance = get_distance(c0=c0,c1=c1,t0=params[0],t1=params[1])

    spline_points = (c0.getD0(params[0]),c1.getD0(params[1]))

    center_point = App.Vector((spline_points[0].x+spline_points[1].x)/2,(spline_points[0].y+spline_points[1].y)/2,(spline_points[0].z+spline_points[1].z)/2)
    
    cross = c0.tangent(params[0])[0].cross(c1.tangent(params[1])[0])
    
    if cross != App.Vector((0,0,0)):

        normal = cross.normalize()
        
    else:
        
        raise ValueError("Cross product results in null vector")
    
    curvature_centers = (c0.centerOfCurvature(params[0]),c1.centerOfCurvature(params[1]))
    
    common_curvature_center = App.Vector((curvature_centers[0][0]-curvature_centers[1][0])/2, (curvature_centers[0][1]+curvature_centers[1][1])/2, (curvature_centers[0][2]+curvature_centers[1][2])/2)
    
    proj = common_curvature_center.sub(center_point).normalize().dot(normal)
    
    if proj < 0:
        
        normal.scale(-1,-1,-1)
       
    # tangents = (c0.tangent(params[0])[0],c1.tangent(params[1])[0])
    
    angle = math.acos(c0.tangent(params[0])[0].dot(c1.tangent(params[1])[0]))
    
    labels = [0,1]
    
    if hasattr(c0,"Label"):
        
        labels[0] = get_label_numbers(c0.Label)
        
    if hasattr(c1,"Label"):
        
        labels[1] = get_label_numbers(c1.Label)
    
    if isinstance(w0,Part.Wire) and isinstance(w1,Part.Wire):
        
        #print("Is wire")
        
        point = intersection_point(curves=[w0,w1],
        splines = [c0,c1],
        parameters=params,
        centers={(0,1):center_point},
        normals={(0,1):normal},
        distances={(0,1):distance},
        limits=((w0.Edges[0].FirstParameter,w0.Edges[0].LastParameter),(w1.Edges[0].FirstParameter,w1.Edges[0].LastParameter)),
        angles={(0,1):angle},
        labels=[l0,l1])
        
    else:
        
         point = intersection_point(curves=[w0,w1],
         splines = [c0,c1],
         parameters=params,
         centers={(0,1):center_point},
         normals={(0,1):normal},
         distances={(0,1):distance},
         limits=((0,1),(0,1)),
         angles={(0,1):angle},
         labels=[l0,l1])

    return point

    #return params,spline_points,center_point,normal,distance
    
    
def calculate_connection_angles(i_point):
    
    i_point.angles = [0]
    
    for k in range(0,len(i_point.curves)):
        
        i_point.angles.append(i_point.splines[0].tangent(i_point.parameters[0]).dot(i_point.splines[k].tangent(i_point.parameters[k])))
       
def merge_intersection_points(i_points):
    
    def get_angle(s1,s2,p1,p2):
        
        angle = s1.tangent(p1).dot(c2.tangent(p2))*180/math.pi
        
        return angle

    curves=[]
    parameters=[]
    centers={}
    normals=[]
    distances={}
    limits = {}
    angles = {}

    all_curves = [c.curves for c in i_points]
    
    flat_curves = [c for sub in all_curves for c in sub]
    
    all_splines = [s.splines for s in i_points]
    
    flat_splines = [s for sub in all_splines for s in sub]
    
    all_parameters = [p.parameters for p in i_points]
    
    flat_parameters = [p for sub in all_parameters for p in sub]
    
    all_labels = [l.labels for l in i_points]
    
    flat_labels = [l for sub in all_labels for l in sub]
    
    all_normals = [list(n.normals.values()) for n in i_points]
    
    flat_normals = [n for sub in all_normals for n in sub]
    
    assert len(flat_curves) == len(flat_splines) == len(flat_parameters)
        
    param_dict = {}
    
    for n in range(0,len(flat_curves)):
        
        if flat_curves[n].Tag in param_dict.keys():
            
            param_dict[flat_curves[n].Tag].append(flat_parameters[n])
            
        else:
            
            param_dict[flat_curves[n].Tag] = [flat_parameters[n]]
            
    for c in param_dict.keys():
        
        param_dict[c] = statistics.mean(param_dict[c])
        
    new_curves = list(param_dict.keys())
    
    new_params = list(param_dict.values())
    
    new_labels = ["" for k in range(0,len(new_curves))]
    
    for c in range(0,len(new_curves)):
        
        for k in range(0,len(flat_curves)):
            
            if flat_curves[k].Tag == new_curves[c]:
                
                new_curves[c] = flat_curves[k]
                
                new_labels[c] = flat_labels[k]
                
                break
                
    new_splines = [get_spline(c) for c in new_curves]
    
    new_tangents = []
        
    for n in range(0,len(new_params)):

        new_tangents.append(new_splines[n].tangent(new_params[n])[0])
        
        new_tangents[n].normalize()
        
        if new_curves[n].Edges[0].LastParameter - new_params[n] < new_params[n] - new_curves[n].Edges[0].FirstParameter:
            
            new_tangents[n].multiply(-1)
        
    new_center = App.Vector([statistics.mean([new_splines[n].getD0(new_params[n]).x for n in range(0,len(new_splines))]),
        statistics.mean([new_splines[n].getD0(new_params[n]).y for n in range(0,len(new_splines))]),
        statistics.mean([new_splines[n].getD0(new_params[n]).z for n in range(0,len(new_splines))])])
        
    new_normal = App.Vector([statistics.mean([flat_normals[n].x for n in range(0,len(flat_normals))]),
        statistics.mean([flat_normals[n].y for n in range(0,len(flat_normals))]),
        statistics.mean([flat_normals[n].z for n in range(0,len(flat_normals))])]).normalize()
        
    if new_center.dot(new_normal) > 0:
        
        new_center.multiply(-1)
       
    #debug_line(new_center,new_normal)

    #for k in range(0,len(new_curves)):
        
    #    Draft.makePoint(new_splines[k].getD0(new_params[k]))
        
    #    debug_line(new_center,new_tangents[k])

    new_point = intersection_point(curves=new_curves,splines=new_splines,parameters = new_params,labels=new_labels,centers=[new_center],tangents=new_tangents,normals=[new_normal])

    return new_point
    

    
def get_point_net(sel,tolerance=1,limit_tolerance=0.1,merge_distance=0.1,merge=True):
    
    curves = sel
    
    tested = []
    
    points = {}
    
    curves_dict = {}
    
    for e in curves:
        
        key = int(get_label_numbers(e.Label,""))
        
        curves_dict[key] = e
    
    for c in curves_dict.keys():
        
        for d in curves_dict.keys():
            
            if c != d:
                
                if not (c,d) in tested and not (d,c) in tested:
                    
                    tested.append((c,d))
                    
                    try:
        
                        #params,spline_points,center_point,normal,distance = get_closest_point(curves[c],curves[d])
                        
                        point = get_closest_point(curves_dict[c],curves_dict[d])
                        
                        close = math.sqrt((point.splines[0].getD0(point.parameters[0]).x-point.splines[1].getD0(point.parameters[1]).x)**2 + (point.splines[0].getD0(point.parameters[0]).y-point.splines[1].getD0(point.parameters[1]).y)**2+(point.splines[0].getD0(point.parameters[0]).z-point.splines[1].getD0(point.parameters[1]).z)**2) < tolerance
                    
                        within_limit = point.limits[0][0] - limit_tolerance <= point.parameters[0] <= point.limits[0][1] +limit_tolerance and point.limits[1][0]-limit_tolerance <= point.parameters[1] <= point.limits[1][1]+limit_tolerance
                    
                        #print("Limits:",point.limits,point.parameters,within_limit)
                    
                        if close and within_limit:
        
                            points[(c,d)] = point
                            
                            #print(point.parameters[0],point.parameters[1])
                            
                    except ValueError:
                        
                        pass
                        
    to_remove = []
    
    #print("Points",points)
    
    if merge:
    
        new_points = {}
        
        k = list(points.keys())
                            
        for p in k:
            
            close_points = []
            
            close_points_curves = []
            
            if p in points.keys():
            
                for q in points.keys():
                    
                    different = p != q
                    
                    dist = math.sqrt((points[p].centers[(0,1)].x-points[q].centers[(0,1)].x)**2 + (points[p].centers[(0,1)].y-points[q].centers[(0,1)].y)**2 + (points[p].centers[(0,1)].z-points[q].centers[(0,1)].z)**2)
                    
                    #print(f"Distance {p} - {q}: {dist}")
                    
                    close =  dist < tolerance
                    
                    if close:
                        
                        close_points.append(points[q])
                        
                        for r in q:
                            
                            if not r in close_points_curves:
                                
                                close_points_curves.append(r)
                        
                #print("P:",close_points)            
                
                new_points[tuple(close_points_curves)] = close_points[0]
                
                new_points[tuple(close_points_curves)] = merge_intersection_points(close_points)
                
                #new_points[close_curves_numbers].splines = [curves_dict[c] for c in close_points_curves]
                
                #new_points[close_curves_numbers].parameters = [curves_dict[c].parameters for c in close_points_curves]
                
                #new_points[close_curves_numbers].labels = close_curves_numbers
                
                #new_points[close_curves_numbers].angles[(0,0)] = 0
                
                #for k in close_points.keys():
                
                #    new_points[close_curves_numbers].angles[k] = close_points[k].angles[(0,1)]
                
                k = tuple(points.keys())
                
                for c in close_points[1:]:
                    
                    for p in k:
                        
                        if k in points.keys():
                
                            if points[p] == c:
                            
                                points.pop(p)
                
        print("Points removed:",to_remove, "\n Points left:",points)
        
        #print(new_points)

        return curves_dict, new_points
    
    else:
        
        return curves_dict, points
    
def generate_normals(sel,tolerance=1,group_label="point_net_normals"):
     
    c, p = get_point_net(sel,tolerance=tolerance)
     
    doc = App.activeDocument()
        
    group = find_or_create(doc,label=f"{group_label}$",objtype="App::DocumentObjectGroup")
    
    normals = []
     
    for k in p.keys():
        
        line = Draft.make_line(App.Vector(p[k].centers[(0,1)]),App.Vector(p[k].centers[(0,1)]).add(App.Vector(p[k].normals[(0,1)])))
         
        normals.append(line)
        
        group.addObject(line)
         
    doc.recompute()
    
    return normals
    
    
def autopipe(net,pipe_sketch,subtractive=False,group_label="point_net_pipes",body_label="pipe_frame",aux_net=[],piped=[]):

    doc = App.activeDocument()
    
    App.Console.PrintLog(f"Piping sketch {pipe_sketch.Label}")
    
    pipe_group = find_or_create(doc,label=f"/^{group_label}$",objtype="App::DocumentObjectGroup")
        
    assert type(pipe_group) == App.DocumentObjectGroup
    
    c = get_splines(net)
    
    #print(curves)
    
    wires = {}
    
    curves_dict = {}
    
    aux_shapes = {}
    
    pipe_objs = []
    
    pipe_bodies = []
    
    for e in net:
        
        key = int(get_label_numbers(e.Label))
        
        wires[key] = e
        
        curves_dict[key] = get_spline(e)
        
    for a in aux_net.values():
        
        key = int(get_label_numbers(a.Label))
        
        aux_shapes[key] = a
        
    #print(wires.keys(),curves_dict,aux_shapes.keys(),aux_shapes)
        
    assert wires.keys() == aux_shapes.keys() or not aux_net 
    
    nodes = []
    
    for c in wires.keys():
    
        #print(c,piped)
    
        if c in piped:
        
            pipe_body = doc.addObject("PartDesign::Body",body_label)
            
            pipe_group.addObject(pipe_body)
            
            pipe_body.AllowCompound = True
        
            binder = doc.addObject("PartDesign::SubShapeBinder","SubShapeBinder")
            
            #print(wires[c])
            
            binder.Support = wires[c]
        
            datum = doc.addObject("Part::DatumPlane","DatumPlane")
            
            sketch = doc.copyObject(pipe_sketch)
            
            pipe_body.addObject(sketch)
            
            pipe_body.addObject(binder)
            
            pipe_body.addObject(datum)
            
            datum.Visibility = False
            
            binder.Visibility = False
            
            sketch.Visibility = False
            
            sketch.AttachmentSupport = [(datum)]
            
            pos = App.Vector(curves_dict[key].getD0(0))
            
            if not subtractive:
            
                pipe = doc.addObject("PartDesign::AdditivePipe")
                
                pipe_body.addObject(pipe)
                
            else:
            
                pipe = doc.addObject("PartDesign::SubtractivePipe")
                
                pipe_body.addObject(pipe)
                
            pipe.Profile = sketch
            
            pipe.Spine = (binder,"Edge001")
            
            if not aux_net:
            
                pipe.Mode = "Frenet"
                
            else:
                
                pipe_body.addObject(aux_binder := doc.addObject("PartDesign::SubShapeBinder","Aux_SubShapeBinder"))
                
                pipe.Mode = "Auxiliary"
                
                aux_curve = get_spline(aux_shapes[c])
               
                rot1 = App.Rotation(App.Vector(0,1,0),aux_curve.getD0(0).sub(curves_dict[c].getD0(wires[c].Shape.Edges[0].FirstParameter)))
                
                #print(curves_dict[c].tangent(wires[c].Shape.Edges[0].FirstParameter))
                
                #rot2 = App.Rotation(rot1.multVec(App.Vector(0,0,1)),curves_dict[c].tangent(wires[c].Shape.Edges[0].FirstParameter)[0])
                
                rot1 = App.Rotation(App.Vector(0,0,1),curves_dict[c].tangent(wires[c].Shape.Edges[0].FirstParameter)[0])
                
                angle = math.acos(App.Vector(0,1,0).dot(aux_curve.getD0(0).sub(curves_dict[c].getD0(wires[c].Shape.Edges[0].FirstParameter))))
                
                rot2 = App.Rotation(curves_dict[c].tangent(wires[c].Shape.Edges[0].FirstParameter)[0],Radian=angle)
                
                
                datum.Placement.Base = curves_dict[c].getD0(wires[c].Shape.Edges[0].FirstParameter)
                
                #datum.Placement.Rotation = rot2.multiply(rot1)
                
                tangent = Draft.make_line(datum.Placement.Base,datum.Placement.Base.add(curves_dict[c].tangent(wires[c].Shape.Edges[0].FirstParameter)[0]))
                
                normal = Draft.make_line(datum.Placement.Base,aux_curve.getD0(0))
                
                #line = Draft.make_line(datum.Placement.Base,datum.Placement.Base.add(datum.Placement.Rotation.multVec(App.Vector(0,1,0))))
                
                tangent.Label,normal.Label = "tangent","normal"
                
                datum.MapMode = "OZY"
                
                datum.AttachmentSupport = [(tangent,("Vertex1",)),(tangent,("Edge1",)),(normal,("Edge1",))]
                
                #pipe_group.addObject(line)
                
                pipe_group.addObject(normal)
                
                pipe_group.addObject(tangent)
                
                #print(datum.Placement.Rotation)
                
                aux_binder.Support = aux_shapes[c]
                
                aux_binder.Visibility = False
                
                pipe.AuxiliarySpine = aux_binder
            
            pipe.Visibility = True
            
            pipe_objs.append(pipe)
            
            pipe_bodies.append(pipe_body)
        
    doc.recompute()
    
    return pipe_group, pipe_bodies, pipe_objs
        
        


def autonode(points,node_object,group_label="point_net_nodes",orientations={},offset=(0,0,0)):
    
    doc = App.activeDocument()
    
    node_bodies = []
    
    node_group = find_or_create(doc,label=f"{group_label}$",objtype="App::DocumentObjectGroup")
    
    assert len(orientations) in (0,len(points))
    
    App.Console.PrintLog(f"Autonode placing object {node_object.Label}")
        
    for p in points.keys():
        
            App.Console.PrintMessage("Copying.")
                
            c = doc.copyObject(node_object)
            
            cs = node_group.addObject(doc.addObject("Part::LocalCoordinateSystem"))[0]
            
            node_group.addObject(c)
            
            pos = App.Vector(points[p].centers[0])
            
            normal = points[p].normals[0]
            
            #ypr = (math.atan2(normal.x,normal.y)*180/math.pi,math.asin(-normal.z)*180/math.pi,0)
            
            #rot = App.Rotation(ypr[0],ypr[1],ypr[2])
            
            rot = App.Rotation(App.Vector((0,0,1)),normal)
            
            #print(points[p].tangent_0)
            
            rot2 = App.Rotation(rot.multVec(App.Vector(1,0,0)),points[p].splines[0].tangent(points[p].parameters[0])[0])
            
            if p in orientations.keys():
            
                rot3 = App.Rotation("xyz",0,0,orientation[p])
                
            else:
                
                rot3 = App.Rotation("xyz",0,0,0)
                
                print(f"Intersection {p} has no rotation, defaulting to 0°")
            
            #print(ypr,rot)
            
            #c.Placement = App.Placement(pos,rot3.multiply(rot2.multiply(rot)),App.Vector(0,0,0))
            
            #c.Placement = App.Placement(pos,rot2.multiply(rot),App.Vector(0,0,0))
            
            cs.Placement = App.Placement(pos,rot,App.Vector(0,0,0))
            
            cs.Placement.Base = cs.Placement.Base.add(rot.multVec(App.Vector(offset)))
            
            c.Label = f"{group_label}_{str(p[0])}-{str(p[1])}"
            
            c.Placement = cs.Placement
            
            node_bodies.append(c)
            
    return node_group, node_bodies
            
def split_net(net,tolerance=1,min_length=0.5,group_label="split_curves"):
    
    doc = App.activeDocument()
    
    split_group = find_or_create(doc,label=f"{group_label}$",objtype="App::DocumentObjectGroup")
    
    curves, points = get_point_net(net,tolerance=tolerance,merge=False)
    
    App.Console.PrintLog(f"Splitting curve network {net}")
    
    curves = curves.values()
    
    split_list, split_edges = [], []
    
    for c in range(0,len(curves)):
        
        close_points = []
        
        cut_points = []
        
        for k in points.keys():
            
            if c in k:
                
                close_points.append(points[k])
                
                cut_points.append(points[k].parameters[0] if c == k[0] else points[k].parameters[1])
                
        cut_points = list(filter(lambda p: 0<p<1, cut_points))
                
        split_curves = net[c].Shape.split(cut_points)
        
        for sc in split_curves.Edges:
            
            if sc.Length > min_length:
            
                s = doc.addObject("Part::Feature","curve_split")
            
                split_group.addObject(s)
            
                wire = Part.Wire(sc)
            
                s.Shape = wire
            
                split_list.append(s)
            
    doc.recompute()
    
    return split_list, split_curves.Edges
    
def place_at_parameters(place_object,curves,parameters,subtractive=False,normal="frenet",group_label=""):

    doc = App.activeDocument()
    
    curves = get_splines(curves)
    
    obj_group = find_or_create(doc,label=f"{group_label}$",objtype="App::DocumentObjectGroup")
        
    for c in curves:
        
        for p in parameters:
        
            if not 0<p<1:
            
                print(f"Parameter {p} outside of curve.")
    
            o = doc.copyObject(place_object,False)
            
            point = curve.getD0(p)
            
            curvature_center = curve.centerofCurvature(p)
            
            normal_vector = curvature_center.subtract(point).normalize()
            
            body.addObject(o)
            
            if normal == "frenet":
            
                rotation = App.Rotation(App.Vector(0,0,0),normal_vector)
            
            placement = App.Placement(point,rotation,App.Vector(0,0,0))
            
def generate_layered_node(frame_xsection,conductor_xsections,conductor_angles=[],conductor_angle_offsets=[],conductor_z_offsets=[],placement=App.Placement(App.Vector(0,0,0),App.Rotation(App.Vector(1,0,0),Degree=0)),body_label="layered_node",z_offset=0):

    # Revolves a "frame" structural cross-section and a "conductor" cross-section into a layered node
    
    App.Console.PrintLog(f"Generating layered node at with conductor sketches {[c.Label for c in conductor_xsections]}, frame sketches")
    
    doc = App.activeDocument()
        
    frame_body = find_or_create(doc,label=f"{body_label}_frame$",objtype="PartDesign::Body")
        
    cond_body = find_or_create(doc,label=f"{body_label}_conductor$",objtype="PartDesign::Body")
        
    cond_body.AllowCompound = True
    
    assert len(conductor_angle_offsets) == len(conductor_angles) == len(conductor_z_offsets)
    
    if isinstance(placement,App.Placement):
        
        placement = placement
        
    elif str(type(placement)) == str(intersection_point):
        
        #print("Is intersection_point")
        
        n_vec = App.Vector(0,0,1)
        
        rot = App.Rotation(n_vec,placement.normals[0])
        
        n_vec = rot.multVec(n_vec)
        
        #debug_line(origin=placement.center,direction=rot.multVec(App.Vector(1,0,0)),label="n_debug_1")
        
        #print(placement.tangent_0)
        
        rot2 = App.Rotation(rot.multVec(App.Vector(1,0,0)),placement.splines[0].tangent(placement.parameters[0])[0])
        
        #debug_line(origin=placement.center,direction=rot2.multiply(rot).multVec(App.Vector(1,0,0)),label="n_debug_2")
        
        placement = App.Placement(App.Vector(placement.centers[0]),rot2.multiply(rot))
        
        placement.Base = placement.Base.add(n_vec*(z_offset))
        
    
    frame_body.Origin.Placement = placement
    
    cond_body.Origin.Placement = placement
    
    for rev in range(0,len(conductor_angles)):
        
        cond_body.addObject(cond_cs := doc.addObject("Part::LocalCoordinateSystem",f"cond_origin_{rev}"))
        
        ax = placement.Rotation.multVec(App.Vector(0,0,1))
      
        cond_cs.Placement = App.Placement(placement.Base.add(ax*(conductor_z_offsets[rev]+z_offset)),App.Rotation(ax,Degree=conductor_angle_offsets[rev]).multiply(placement.Rotation))
        
        #debug_line(cond_cs.Placement.Base,ax,label="axis_debug")
        
        #debug_line(cond_cs.Placement.Base,cond_cs.Placement.Rotation.multVec(App.Vector(0,0,1)),label="angle_debug")
    
        cond_body.addObject(rev_obj := doc.addObject("PartDesign::Revolution"))
        
        cond_body.addObject(sk := doc.copyObject(conductor_xsections[rev]))
        
        att = (cond_cs,[cond_cs.OriginFeatures[4].Name])
        
        sk.AttachmentSupport = att
        
        #cond_cs.AttachmentOffset = App.Placement(App.Vector(0,0,conductor_z_offsets[rev]),rot2.multiply(rot.multiply(App.Rotation("xyz",0,0,conductor_angle_offsets[rev]))))
        
        #sk.AttachmentOffset = App.Placement(App.Vector(0,0,conductor_z_offsets[rev]),App.Rotation(1,0,0,0))
        
        rev_obj.Profile = sk
        
        rev_obj.Angle = conductor_angles[rev]
        
        rev_obj.ReferenceAxis = (sk, ['V_Axis'])
        
    frame_obj = doc.addObject("PartDesign::Revolution")
    
    frame_body.addObject(frame_obj)
    
    frame_obj.Angle = 360
    
    frame_body.addObject(frame_sketch := doc.copyObject(frame_xsection))
    
    frame_sketch.AttachmentSupport = [(frame_body.Origin,(frame_body.Origin.OriginFeatures[4].Name,))]
     
    frame_obj.Profile = frame_sketch
    
    frame_obj.ReferenceAxis = (frame_sketch, ['V_Axis'])
    
    doc.recompute()
    
    return (frame_body, cond_body)
        
        
def autoconstruct(net,node_objects=[],pipes=[],aux_curves=[],tolerance=1,split=False,interpolate_normals=True,center=App.Vector(0,0,0),orientations={},node_group_names=[],pipe_group_names=[],pipe_body_names=[]):
    
    doc = App.activeDocument()
    
    if split:
        
        split_wires, split_edges = split_net(net)
        
    if interpolate_normals:
        
        aux = interpolate_aux_curves(curves=net,mode="center",center=center)
        
    else:
        
        assert len(aux_curves) == len(net)
        
        aux = aux_curves
        
    assert len(node_group_names) in (0,len(node_objects)) and len(pipe_group_names) in (0,len(pipes)) and len(pipe_body_names) in (0,len(pipes))
        
    for node in range(0,len(node_objects)):
        
        c, p = get_point_net(net)[0]
        
        node_group, node_bodies = autonode(points=p,node_object=node_objects[node],orientations=orientations,group_label=node_group_names[node] if node_group_names else "node_group")
        
        if isinstance(node_bodies[0],Part.Feature):
        
            node_bodies[-1].addObject(boolean_obj:=doc.addObject("PartDesign::Boolean",f"{node_group_names[node]}_bool"))
            
            node_bodies[-1].AllowCompound = True
        
            boolean_obj.Group = node_bodies[0:-1]
        
            boolean_obj.Type = "Fuse" 
        
    for pipe in range(0,len(pipes)):
        
        pipe_groups, pipe_bodies, pipe_objects = autopipe(net=net,pipe_sketch=pipes[pipe],aux_net=aux.values(),group_label=pipe_group_names[pipe] if pipe_group_names else "pipe_group",body_label=pipe_body_names[pipe] if pipe_body_names else "pipe_body")
        
        #return pipe_objects
        
        pipe_bodies[-1].addObject(boolean_obj:=doc.addObject("PartDesign::Boolean",f"{pipe_body_names[pipe]}_bool"))
        
        boolean_obj.Group = pipe_bodies[0:-1]
        
        boolean_obj.Type = "Fuse" 
        
        
    doc.recompute()
    
                
def interpolate_aux_curves(curves,normal_points=[],mode="points",center=None,degree=5,curve_label="aux_curve",group_label="interpolated_aux_curves"):
    
    # Modes: "points" - interpolates from given normal points
    # "center" - usess normals relative to center point vector

    curve = get_splines(curves)[0]
    
    assert not any(list(map(lambda x: not isinstance(x,intersection_point),normal_points)))
    
    doc = App.activeDocument()
    
    #doc.addObject("Part::Feature","interp_curve")
    
    #print(group_label)
    
    aux_curves = {}
    
    group = find_or_create(doc,label=f"{group_label}$",objtype="App::DocumentObjectGroup")
        
    if mode == "points":
        
        assert len(normal_points) > 1
        
        curves = get_splines(curves)
        
        for c in range(0,len(curves)):
            
            group.addObject(interp_curve:=doc.addObject("Part::Feature",f"{curve_label}{c}")) 
        
            assert isinstance(center,App.Vector) and type(curve_shapes[c]) == Part.BSplineCurve and type(curves[c].Shape.Edges[0]) == Part.Edge
            
            limits = (curves[c].Shape.Edges[0].FirstParameter,curves[c].Shape.Edges[0].LastParameter)
            
            points = [limits[0]+(((limits[1]-limits[0])*p)/degree)for p in range(0,degree+1)]
        
    elif mode == "center":
        
        for c in range(0,len(curves)):
            
            #print(curve,curve.Label)
            
            curve_shapes = get_splines(curves)
            
            #print(center,type(curve_shapes[c]))
        
            assert isinstance(center,App.Vector) and type(curve_shapes[c]) == Part.BSplineCurve and type(curves[c].Shape.Edges[0]) == Part.Edge
            
            #group.addObject(interp_curve:=doc.addObject("Part::Feature",f"{curve_label}{c}")) 
            
            limits = (curves[c].Shape.Edges[0].FirstParameter,curves[c].Shape.Edges[0].LastParameter)
            
            points = [limits[0]+(((limits[1]-limits[0])*p)/degree)for p in range(0,degree+1)]
            
            #print(points,limits)
            
            vectors = [curve_shapes[c].getD0(p) for p in points]
            
            def get_normal_vector(point_0,point_1):
                
                return point_1.add(point_1.sub(point_0).normalize())
            
            normal_vectors = [get_normal_vector(center,v) for v in vectors]
            
            #print(normal_vectors)
            
            temp_obj = Draft.make_wire(normal_vectors)
            
            doc.recompute()
            
            #print(temp_obj.Shape.Vertexes)
            
            label_number = "".join([k if k.isdigit() else "" for k in curves[c].Label.lstrip("0")])
            
            label = f"{curve_label}_{label_number}"
                
            curves_wb.approximate.Approximate(approx_curve:=doc.addObject("Part::FeaturePython",label),temp_obj)
            
            curves_wb.approximate.ViewProviderApp(approx_curve.ViewObject)
            
            group.addObject(approx_curve)
            
            group.addObject(temp_obj)
            
            temp_obj.Visibility = False
            
            aux_curves[label] = approx_curve
            
            #interp_curve.Shape = Part.Wire()
            
            #interp_curve.Shape.Edges  = [Part.Edge(curve)]
            
    doc.recompute()
            
    return group, aux_curves
    
    
# Format: (z offset, z distance (check if unused), (angle, angle offset, z offset), (angle1, angle offset1, z offset1) ...)
    

offsets = (4.6,1,-2.6)
    
    
default_node_connections = {
"1-2-55":(-1,0,(210,-180,4.2),(40,-200,1),(360,-200,-2.2)),
"16-44-55":(-1,0,(210,-180,4.2),(40,-200,1),(360,-200,-2.2)),
"22-55":(-1,0,(210,-180,4.2),(40,-200,1),(360,-200,-2.2)),
"1-5":(-1,0,(210,-180,4.2),(40,-200,1),(360,-200,-2.2)),
"2-3-21":(-1,0,(210,-180,4.2),(40,-200,1),(360,-200,-2.2)),
"3-4-23-24":(-1,0,(210,-180,4.2),(40,-200,1),(360,-200,-2.2)),
"4-51":(-1,0,(210,-180,4.2),(40,-200,1),(360,-200,-2.2)),
"5-6-43-44":(-1,0,(210,-180,4.2),(40,-200,1),(360,-200,-2.2)),
"6-7-10-11":(-1,0,(210,-180,4.2),(40,-200,1),(360,-200,-2.2)),
"7-8-25-26":(-1,0,(210,-180,4.2),(40,-200,1),(360,-200,-2.2)),
"8-33-54":(-1,0,(210,-180,4.2),(40,-200,1),(360,-200,-2.2)),
"9-10-15-16":(-1,0,(210,-180,4.2),(40,-200,1),(360,-200,-2.2)),
"9-17-21":(-1,0,(210,-180,4.2),(40,-200,1),(360,-200,-2.2)),
"11-12-40-41":(-1,0,(210,-180,4.2),(40,-200,1),(360,-200,-2.2)),
"12-37":(-1,0,(210,-180,4.2),(40,-200,1),(360,-200,-2.2)),
"13-29-32":(-1,0,(210,-180,4.2),(40,-200,1),(360,-200,-2.2)),
"13-14-53-54":(-1,0,(210,-180,4.2),(40,-200,1),(360,-200,-2.2)),
"14-15-26-27":(-1,0,(210,-180,4.2),(40,-200,1),(360,-200,-2.2)),
"17-18-27-28":(-1,0,(360,-180,4.2),(360,-200,-2.2)),
"18-19-52-53":(-1,0,(210,-180,4.2),(40,-200,1),(360,-200,-2.2)),
"19-20-29-30":(-1,0,(210,-180,4.2),(40,-200,1),(360,-200,-2.2)),
"20-34":(-1,0,(210,-180,4.2),(40,-200,1),(360,-200,-2.2)),
"22-24":(-1,0,(210,-180,4.2),(40,-200,1),(360,-200,-2.2)),
"23-28-50":(-1,0,(210,-180,4.2),(40,-200,1),(360,-200,-2.2)),
"25-39-41":(-1,0,(210,-180,4.2),(40,-200,1),(360,-200,-2.2)),
"30-49":(-1,0,(210,-180,4.2),(40,-200,1),(360,-200,-2.2)),
"31-32-34-35":(-1,0,(210,-180,4.2),(40,-200,1),(360,-200,-2.2)),
"31-46":(-1,0,(210,-180,4.2),(40,-200,1),(360,-200,-2.2)),
"33-35-36":(-1,0,(210,-180,4.2),(40,-200,1),(360,-200,-2.2)),
"36-37-38-39":(-1,0,(210,-180,4.2),(40,-200,1),(360,-200,-2.2)),
"38-46":(-1,0,(210,-180,4.2),(40,-200,1),(360,-200,-2.2)),
"40-43":(-1,0,(210,-180,4.2),(40,-200,1),(360,-200,-2.2)),
"49-50-51-52":(-1,0,(210,-180,4.2),(40,-200,1),(360,-200,-2.2))
}


test_node_connections = {
"1-2-55":(-1,0,(360,-200,offsets[1])),
"16-44-55":(-1,0,(360,-200,offsets[1])),
"22-55":(-1,0,(360,-180,offsets[1])),
"1-5":(-1,0),
"2-3-21":(-1,0),
"3-4-23-24":(-1,0,(36,-200,offsets[1])),
"4-51":(-1,0),
"5-6-43-44":(-1,0),
"6-7-10-11":(-1,0,(360,-200,offsets[1]),(360,-200,offsets[0])),
"7-8-25-26":(-1,0,(360,-180,offsets[0]),(360,-200,offsets[1])),
"8-33-54":(-1,0,(90,-113,offsets[0]),(90,113,offsets[0])), # split same level
"9-10-15-16":(-1,0,(360,-180,offsets[0]),(360,-200,offsets[1])),
"9-17-21":(-1,0),
"11-12-40-41":(-1,0,(360,-180,offsets[0])),
"12-37":(-1,0,(360,-180,offsets[1])),
"13-29-32":(-1,0,(360,-180,offsets[0]),(360,-200,1),(360,-200,-2.2)),
"13-14-53-54":(-1,0,(360,-180,offsets[0]),(360,-200,offsets[1])),
"14-15-26-27":(-1,0,(100,-185,offsets[0]),(100,-5,offsets[0])), # split same level
"17-18-27-28":(-1,0,(360,-180,offsets[0]),(360,-200,offsets[2])),
"18-19-52-53":(-1,0,(360,-200,offsets[1]),(360,-200,offsets[0])),
"19-20-29-30":(-1,0,(360,-180,offsets[0])),
"20-34":(-1,0,(360,-180,offsets[1])),
"22-24":(-1,0,(360,-180,offsets[1])),
"23-28-50":(-1,0,(360,-200,offsets[1])),
"25-39-41":(-1,0,(360,-180,offsets[0]),(360,-200,offsets[1]),(360,-200,offsets[2])),
"30-49":(-1,0),
"31-32-34-35":(-1,0,(360,-180,offsets[0]),(360,-200,offsets[1]),(360,-200,offsets[2])),
"31-46":(-1,0),
"33-35-36":(-1,0),
"36-37-38-39":(-1,0),
"38-46":(-1,0),
"40-43":(-1,0),
"49-50-51-52":(-1,0)
}

pipe_connections = {
"frame":list(range(1,56)),
"frame_3_conductor_3":[32,39],
"frame_3_conductor_2":[7,10,13,16,18,23,24,25,28,34,37,53,55],
"frame_3_conductor_1":[8,11,14,15,19,26,27,29,32,39,41,54]
}

def full_auto(curves=None,node_parameters=default_node_connections):
    
    doc = App.activeDocument()
    
    to_find = {"curves":"curve_split","frame":"frame_3_outer","frame_conductors":"frame_3_conductor_\d","node_frame":"test nodegen frame","node_conductor":"test nodegen conductor","cutout":"curve extrusion base_08mm-test-refinedcut_extended","center":"Center"}
    
    #to_find = {"curves":"curve_split","frame":"frame_3_outer","frame_conductors":"frame_3_conductor_triple","node_frame":"test nodegen frame","node_conductor":"test nodegen conductor","cutout":"curve extrusion base_08mm-test-refinedcut_extended","center":"Center"}
    
    
    
    found = {}
    
    for k in to_find.keys():
        
        found[k] = doc.findObjects(Label=to_find[k])
        
    print(found)
    print({k:len(found[k]) for k in found.keys()})
    
    node_params = {
    }
    
    if not curves:
        
        curves = found["curves"]
    
    net = curve_net(curves,
            sketches={"node_frame":found["node_frame"][0],"node_conductor":found["node_conductor"][0],"frame":found["frame"][0],"frame_conductors":found["frame_conductors"]},
            default_node_params=(-1,0,(210,-180,4.2),(40,-200,1),(360,-200,-2.2)),
            objects={"cutout":found["cutout"][0]},
            center=found["center"][0].Placement.Base,
            object_offsets={"cutout":(0,0,-1)},
            node_params=test_node_connections,
            piped_curves=pipe_connections)
    
    net.generate()