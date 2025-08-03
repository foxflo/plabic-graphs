from itertools import chain,combinations
from collections import deque,OrderedDict, defaultdict
from sys import stdout

"""
#The way to use this code is to first create a symmetric plabic graph using plabic or rect_plabic
plabic_graph = rect_plabic(4) #generate the rectangles symmetric plabic graph corresponding to the top dimensional cell of the positive part of LGr(4)

#then generate all the mutation equivalent symmetric plabic graphs by symmetric mutations at square faces
#furthermore, each symmetric plabic graph corresponds to a point on the tropical lagrangian grassmannian
tropical_vectors, plabic_graphs = tropical_traverse_sym(plabic_graph, 4)
#note that plabic_graphs is a list of pairs (plabic_graph, num) where num is the number of mutations required to reach plabic_graph starting from the rectangles plabic graph

#I've also implemented flow polynomial computations for symmetric plabic graphs
example_graph = plabic_graphs[0][0]
all_flow_polys(example_graph)
#currently doesn't generate output, but could be easily modified to return all the flow polynomials
#currently prints out the minimal exponent vector valuation of each flow polynomial
#collected as vertices of a polytope in polymake format
#we can then compute various combinatorial properties, e.g. whether the volume of this polytope matches the degree of the corresponding variety

#also modified to produce flow polynomial computations for nonsymmetric plabic graphs
#this allows for comparison with the analogous grassmannian version, e.g. between Gr(n,2n) which contains LGr(n,2n) as a subvariety and LGr(n,2n)
all_flow_polys_nonsym(example_graph)
"""
#everything in this file has some sort of "symmetry" coming from the lagrangian grassmannian vs the regular grassmannian, so it works for Gr(n,2n) or LGr(n,2n) only
#should be relatively straightforward to modify this file to work also for regular grassmannians, e.g. no preservation of symmetry.

#caller must guarantee that iterable contains some element satisfying condition, so error checking will not be attempted here
def first(iterable, condition):
    return next(i for i in iterable if condition(i))

#flatten nested iterable
def flatten(nested_iterable):
    return chain.from_iterable(nested_iterable)

#produce list of all plabic graphs (as sage graphs with fixed perfect orientation) with 2n boundary vertices
#each plabic graph parametrizes different cell of totally nonnegative lagrangian grassmannian
def plabic(n):
    le_diagrams = le(n)
    hooks = sorted([hook_from_le(led,n) for led in le_diagrams],key=lambda x:x.num_verts())
    return [plabic_from_hook(hook,n) for hook in hooks]

#produce rectangles plabic graph (for top dimensional cell of totally nonnegative lagrangian grassmannian)
def rect_plabic(n):
    coords = tuple(zip(flatten([[-i]*n for i in range(n)]),[-i for i in range(n)]*n))
    hook = hook_from_le(((),coords),n)
    return plabic_from_hook(hook,n)

#produce le diagrams (to be turned into hook diagrams)
#le diagrams have format(boxes to be filled with 0, order filter (diagram shape))
def le(n):
    x = flatten([[-i]*(n-i) for i in range(n)])
    y = flatten([[j-n+1 for j in range(i,-1,-1)] for i in range(n-1,-1,-1)])
    coords = list(zip(x,y))
    P = Poset([coords, lambda a,b:a[0]<=b[0] and a[1]<=b[1]])
    subsets = chain.from_iterable(combinations(coords,i) for i in range(len(coords)+1))
    filters = set([tuple(P.order_filter(i)) for i in subsets])
    #pairs of (assigned 0 instead of +, original diagram)
    possible_le = flatten([[(i,filt) for i in chain.from_iterable(combinations(filt,i) for i in range(len(filt)+1))] for filt in filters])
    le_diags = filter(lambda x:check_le(x[0]),possible_le)
    return le_diags

#produce hook diagram from le diagram
#le diagram is an iterable consisting of pairs (boxes, diagram)
#where boxes indicate which boxes are assigned 0 instead of +
#and diagram indicates the shape of the containing diagram for boxes
#output is sage directed graph
def hook_from_le(le,n):
    get_sinks_sources(le[1],n)
    zeroes = set(le[0]+tuple([(j,i) for (i,j) in le[0]]))
    vertices = set(le[1]+tuple([(j,i) for (i,j) in le[1]]))
    vertices.update([(-n,-i) for i in range(n)]+[(-i,-n) for i in range(n)])
    vertices = list(vertices.difference(zeroes))
    right_edges = []
    down_edges = []
    for i in vertices:
        if i[0]!=-n and i[1]!=-n:
            right_neighbors = [k for (k,j) in filter(lambda x:x[1]==i[1] and x[0]<i[0],vertices)]
            right_edges += [((max(right_neighbors),i[1]),)+(i,)]
            down_neighbors = [j for (k,j) in filter(lambda x:x[0]==i[0] and x[1]<i[1],vertices)]
            down_edges += [(i,)+((i[0],max(down_neighbors)),)]
    return DiGraph([vertices,right_edges+down_edges])
    
#produce plabic graph from hook diagram
#plabic graphs are planar bicolored 
def plabic_from_hook(hook,n):
    V = set(hook.vertices())
    remaining = set()
    label_counter = 2*n+1
    relabel={}
    while V:
        v=V.pop()
        if hook.degree(v) == 3:
            if set([(v[0],v[1]+i) for i in range(1,n)]).intersection(set(hook.neighbors_in(v))):
                #black vertex
                relabel[v]='b'+str(label_counter)
                relabel[tuple(v[::-1])]='w'+str(label_counter)
                V.remove(tuple(v[::-1]))
                label_counter = label_counter + 1
            elif set([(v[0]+i,v[1]) for i in range(1,n)]).intersection(set(hook.neighbors_out(v))):
                #white vertex
                relabel[v]='w'+str(label_counter)
                relabel[tuple(v[::-1])]='b'+str(label_counter)
                V.remove(tuple(v[::-1]))
                label_counter = label_counter + 1
        else:
            remaining.update([v])
    hook.relabel(relabel)
    while remaining:
        v=remaining.pop()
        if hook.degree(v)==4:
            if tuple(v[::-1])==v:
                inv = hook.neighbors_in(v)
                outv = hook.neighbors_out(v)
                blackV = 'b'+str(label_counter)
                whiteV = 'w'+str(label_counter)
                label_counter = label_counter + 1
                hook.add_vertex(blackV)
                hook.add_vertex(whiteV)
                [hook.add_edge((i,blackV)) for i in inv]
                hook.add_edge((blackV,whiteV))
                [hook.add_edge((whiteV,i)) for i in outv]
                hook.delete_vertex(v)
            else:
                v_t = tuple(v[::-1])
                inv = hook.neighbors_in(v)
                inv_t = hook.neighbors_in(v_t)
                outv = hook.neighbors_out(v)
                outv_t = hook.neighbors_out(v_t)
                blackV = 'b'+str(label_counter)
                whiteV_t = 'w'+str(label_counter)
                label_counter = label_counter + 1
                whiteV = 'w'+str(label_counter)
                blackV_t = 'b'+str(label_counter)
                label_counter = label_counter + 1
                hook.add_vertex(blackV)
                hook.add_vertex(whiteV_t)
                hook.add_vertex(whiteV)
                hook.add_vertex(blackV_t)
                [hook.add_edge((i,blackV)) for i in inv]
                [hook.add_edge((whiteV_t,i)) for i in outv_t]
                hook.add_edge((blackV,whiteV))
                hook.add_edge((blackV_t,whiteV_t))
                [hook.add_edge((whiteV,i)) for i in outv]
                [hook.add_edge((i,blackV_t)) for i in inv_t]
                hook.delete_vertex(v)
                hook.delete_vertex(v_t)
                remaining.remove(v_t)                
        elif hook.degree(v)==2:
            contract_v(hook,v)
    sources = [(-n,-i) for i in range(n)]
    sinks = [(-i,-n) for i in range(n)]
    hook.relabel(dict(zip(sources,[str(p) for p in range(1,n+1)])))
    hook.relabel(dict(zip(sinks,[str(p) for p in range(2*n,n,-1)])))
    #collapse adjacent vertices of the same color
    V = set(hook.vertices()).difference(set([str(p) for p in range(1,2*n+1)]))
    while V:
        v = V.pop()
        n_in = []
        n_out = []
        for i in hook.neighbors_in(v):
            if str(v)[0]==str(i)[0]:
                n_in.append(i)
        for i in hook.neighbors_out(v):
            if str(v)[0]==str(i)[0]:
                n_out.append(i)
        oldCluster = n_in+n_out+[v]
        if oldCluster != [v]:
            newv = str(v)[0]+str(label_counter)
            newv_t = wtob(str(v)[0])+str(label_counter)
            label_counter = label_counter + 1
            hook.add_vertex(newv)
            new_in = set(flatten([hook.neighbors_in(i) for i in oldCluster])).difference(set(oldCluster))
            new_out = set(flatten([hook.neighbors_out(i) for i in oldCluster])).difference(set(oldCluster))
            [hook.add_edge((newv,i)) for i in new_out]
            [hook.add_edge((i,newv)) for i in new_in]
            [hook.delete_vertex(i) for i in oldCluster]
            [V.remove(i) for i in oldCluster[:-1]]
            V.update([newv])
            
            v_t = wtob(str(v)[0])+str(v)[1:]
            n_in_t=[]
            n_out_t=[]
            for i in hook.neighbors_in(v_t):
                if str(v_t)[0]==str(i)[0]:
                    n_in_t.append(i)
            for i in hook.neighbors_out(v_t):
                if str(v_t)[0]==str(i)[0]:
                    n_out_t.append(i)
            oldCluster_t = n_in_t+n_out_t+[v_t]
            hook.add_vertex(newv_t)
            new_in_t = set(flatten([hook.neighbors_in(i) for i in oldCluster_t])).difference(set(oldCluster_t))
            new_out_t = set(flatten([hook.neighbors_out(i) for i in oldCluster_t])).difference(set(oldCluster_t))
            [hook.add_edge((newv_t,i)) for i in new_out_t]
            [hook.add_edge((i,newv_t)) for i in new_in_t]
            [hook.delete_vertex(i) for i in oldCluster_t]
            [V.remove(i) for i in oldCluster_t]
            V.update([newv_t])
    return hook
            
#output: True if filling by 0's results in a valid Le diagram
def check_le(filling):
    for i in filling:
        if i[0]==i[1]: #zero on diagonal
            for j in range(-i[0]):
                if (-j,i[1]) not in filling:
                    return False #zero on diagonal, and plus to left
        for j in range(-i[0]):
            if (-j,i[1]) not in filling: #plus to left of a zero
                for k in range(-i[0],-i[1]):
                    if (i[0],-k) not in filling:
                        return False #plus to left of amd plus above a zero
    return True
    
#output: (sources, sinks)
def get_sinks_sources(filt,n):
    filt = set(filt+tuple([(j,i) for (i,j) in filt]))
    sources=[]
    sinks=[]
    bot_left = (0,-n+1)
    current = (-n+1,0)
    counter = 1
    state=None
    Dir=None
    while current != bot_left:
        if current not in filt and current[0]<0:
            sinks.append(counter)
            current = (current[0]+1,current[1])
            state = 'out'
            Dir = 'left'
        elif current not in filt and current[0]==0:
            if state == 'out':
                if Dir == 'down':
                    sources.append(counter)
                elif Dir == 'left':
                    sinks.append(counter)
                    counter = counter + 1
                    sources.append(counter)
            elif state == 'in':
                sinks.append(counter)
                counter = counter + 1
                sources.append(counter)
            current =  (current[0],current[1]-1)
            state = 'out'
            Dir = 'down'
        elif current in filt and current[1]>-n+1:
            sources.append(counter)
            current = (current[0],current[1]-1)
            state = 'in'
            Dir = 'down'
        elif current in filt and current[1]==-n+1:
            if state == 'out':
                sources.append(counter)
                counter = counter + 1
                sinks.append(counter)
            elif state == 'in':
                if Dir == 'down':
                    sources.append(counter)
                    counter = counter + 1
                    sinks.append(counter)
                elif Dir == 'left':
                    sinks.append(counter)            
            current = (current[0]+1,current[1])
            state = 'in'
            Dir = 'left'
        counter=counter+1
    if bot_left in filt:
        if state == 'out':
            if Dir == 'left':
                sources.append(counter)
                sinks.append(counter+1)
        elif state == 'in':
            if Dir == 'down':
                sources.append(counter)
                sinks.append(counter+1)
            elif Dir == 'left':
                sinks.append(counter)
        elif state == None:
            sources.append(counter)
            sinks.append(counter+1)
    elif bot_left not in filt:
        if state == 'out':
            if Dir == 'down':
                sources.append(counter)
            elif Dir == 'left':
                sinks.append(counter)
                sources.append(counter+1)
        elif state == 'in':
            if Dir == 'down':
                sinks.append(counter)
                sources.append(counter+1)
        elif state == None:
            sinks.append(counter)
            sources.append(counter+1)
    return (sources,sinks)
    
#switch w and b
def wtob(i):
    return 'w' if i=='b' else 'b'

#output list of lists of symmetric pairs of faces of the graph
def find_sym_squares(myGraph):
    faces = myGraph.faces()
    for face in faces:
        for edge in face:
            if edge[::-1] in face:
                face.remove(edge)
                face.remove(edge[::-1])
    
    squares = list(filter(lambda x:len(x)==4,faces))
    vert_sq = dict(zip([tuple(sorted([v[0] for v in square])) for square in squares], squares))
    face_pairs = []
    for square in squares:
        vertices = tuple(sorted([v[0] for v in square]))
        vertices_t = tuple(sorted([wtob(v[0])+v[1:] for v in vertices]))
        if vertices == vertices_t:
            face_pairs.append([square,square])
        elif vert_sq[vertices_t]!=None and vert_sq[vertices]!=None:
            face_pairs.append([square,vert_sq[vertices_t]])
            vert_sq[vertices] = None
            vert_sq[vertices_t] = None
    return face_pairs    
    
#find graph edges in a face (the face comes from Graph.faces(), which gives a traversal of the face in the underlying undirected graph)
def edges_from_face(myGraph,face):
    corrected = []
    for edge in face:
        if not myGraph.has_edge(edge):
            corrected.append(edge[::-1])
        else:
            corrected.append(edge)
    return corrected

#check that the oriented graph is a perfect orientation
def check_orientation(myGraph):
    for v in myGraph.vertices():
        if str(v)[0]=='b':
            if len(myGraph.neighbors_out(v)) != 1:
                return False
        elif str(v)[0]=='w':
            if len(myGraph.neighbors_in(v)) != 1:
                return False
    return True

#contract degree 2 vertex v in myGraph by connecting its neighbors
def contract_v(myGraph,v):
    inv = myGraph.neighbors_in(v)
    outv = myGraph.neighbors_out(v)
    myGraph.add_edge((inv[0],outv[0]))
    myGraph.delete_vertex(v)
    
#contract edge of plabic graph whose vertices have the same color
def contract_e(myGraph,e):
    inv = myGraph.neighbors_in(e[0])
    outv = myGraph.neighbors_out(e[0]) #should contain e[1]
    for v in inv:
        if v != e[1]:
            myGraph.add_edge(v,e[1])
    for v in outv:
        if v != e[1]:
            myGraph.add_edge(e[1],v)
    myGraph.delete_vertex(e[0])
    
#face is a list of length 2, the first is a square face, and the second is the same square face with w exchanged for b and vice versa
def sym_sq_move(myGraph,sq_face,n):
    used_labels = set([int(i[1:]) for i in set(myGraph.vertices()).difference(set([str(p) for p in range(1,2*n+1)]))])
    max_label = max(used_labels)+1
    unused_labels = set([str(p) for p in range(2*n+1,max_label)]).difference(set([str(p) for p in used_labels]))
    sq_verts = set(flatten(map(lambda x:[i[0] for i in x],sq_face)))
    temp = sq_verts.copy() #vertices to check against
    new_verts = {}
    unique = {} #does this vertex force an orientation on the new square
    while sq_verts: #add new vertices for square
        label = None
        v = sq_verts.pop()
        if unused_labels:
            label = unused_labels.pop()
        else:
            label = str(max_label)
            max_label += 1
        v_t = wtob(v[0])+str(v[1:])
        sq_verts.remove(v_t)
        newv = wtob(v[0])+str(label)
        newv_t = v[0]+str(label)
        new_verts[v] = newv
        new_verts[v_t] = newv_t
        myGraph.add_vertex(newv)
        myGraph.add_vertex(newv_t)
        if v[0]=='b': #unique outgoing edge
            if myGraph.neighbors_out(v)[0] not in temp or (myGraph.neighbors_out(v)[0] == 'w'+v[1:] and sq_face[0]!=sq_face[1]):    
                myGraph.add_edge((newv,v))
                myGraph.add_edge((v_t,newv_t))
                unique[newv] = False
                unique[newv_t] = False
            else: 
                myGraph.add_edge((v,newv)) #unique incoming to white vertex
                myGraph.add_edge((newv_t,v_t)) #unique outgoing edge to black vertex
                unique[newv] = True
                unique[newv_t] = True
        elif v[0]=='w': #unique incoming edge
            if myGraph.neighbors_in(v)[0] not in temp or (myGraph.neighbors_in(v)[0] == 'b'+v[1:] and sq_face[0]!=sq_face[1]):
                myGraph.add_edge((v,newv))
                myGraph.add_edge((newv_t,v_t))
                unique[newv] = False
                unique[newv_t] = False
            else:
                myGraph.add_edge((newv,v))
                myGraph.add_edge((v_t,newv_t))
                unique[newv] = True
                unique[newv_t] = True
    #all new vertices should be added at this point
    #now connect new vertices and disconnect old vertices
    old_edges = deque(set(flatten(sq_face)))
    while old_edges:
        edge = old_edges.popleft()
        v0 = edge[0]
        v1 = edge[1]
        newv0 = new_verts[v0]
        newv1 = new_verts[v1]
        if unique[newv0] == True:
            if newv0[0] == 'b':
                myGraph.add_edge((newv1,newv0))
            else:
                myGraph.add_edge((newv0,newv1))
        elif unique[newv1] == True:
            if newv1[0] == 'b':
                myGraph.add_edge((newv0,newv1))
            else:
                myGraph.add_edge((newv1,newv0))
        else: #the orientation of the edge is not determined by the previous part
            if newv0[0]=='b':
                if len(myGraph.neighbors_out(newv0))==1 or len(myGraph.neighbors_in(newv1))==1:#unique incoming edge
                    myGraph.add_edge((newv1,newv0))
                else: #edge direction may be ambiguous
                    if myGraph.degree(newv0) == 2:
                        myGraph.add_edge((newv0,newv1))                    
                    else:
                        old_edges.append(edge)
            else: #newv0[0]=='w'
                if len(myGraph.neighbors_in(newv0))==1 or len(myGraph.neighbors_out(newv1))==1: #unique outgoing edge                
                    myGraph.add_edge((newv0,newv1))
                else: #edge direction may be ambiguous
                    if myGraph.degree(newv0) == 2:
                        myGraph.add_edge((newv1,newv0))
                    else:
                        old_edges.append(edge)
    correct_edges = map(lambda x:edges_from_face(myGraph,x),sq_face)
    [myGraph.delete_edge(edge) for edge in set(flatten(correct_edges))]
    #new graph should be good to go
    #now get rid of interior degree two vertices
    V = set(myGraph.vertices())
    while V:
        v = V.pop()
        if myGraph.degree(v) == 2: #do a symmetric reduction
            v_t = wtob(v[0])+v[1:]
            if myGraph.neighbors_in(v)[0][0] not in {'b','w'} or myGraph.neighbors_out(v)[0][0] not in {'b','w'}:
                contract_v(myGraph,v)
                contract_v(myGraph,v_t) 
            elif myGraph.has_edge((v,v_t)) or myGraph.has_edge((v_t,v)):
                contract_v(myGraph,v)
                contract_v(myGraph,v_t)
            else:
                v_in = myGraph.neighbors_in(v)[0]
                v_out = myGraph.neighbors_out(v)[0]
                v_t_in = myGraph.neighbors_in(v_t)[0]
                v_t_out = myGraph.neighbors_out(v_t)[0]
                contract_v(myGraph,v)
                contract_v(myGraph,v_t)
                contract_e(myGraph,(v_in,v_out))
                contract_e(myGraph,(v_t_out,v_t_in))
            
#take a planar directed graph and directed path in graph and output vertices to the left of that path (i.e. travelling in the orientation of the path, vertices which are to the left)        
#path should begin and end at vertices labelled by integers, so that it splits the graph into two components
def find_left_vertices(myGraph,myPath,myEmbedding,n):
    if myPath == []:
        return []
    right_verts = []
    if myPath[0][0] != '1': #we will always assume source set 1,..,n
        right_verts.append(str(int(myPath[0][0])-1))
    if myPath[-1][1] != str(2*n):
        right_verts.append(str(int(myPath[-1][1])+1))
    for i in range(len(myPath)-1):
        curr = myPath[i][1]
        neighbors = myEmbedding[curr]
        prev = neighbors.index(myPath[i][0])
        next_ = neighbors.index(myPath[i+1][1])
        #right vertices are those from prev to next
        #left vertices are those from next to prev
        if prev > next_:
            next_ = next_+len(neighbors)
        right_verts = right_verts + [neighbors[j%len(neighbors)] for j in range(prev+1,next_)]
    dummy_graph = myGraph.copy()
    right_verts = set(right_verts).difference(set(flatten([[i[0],i[1]] for i in myPath])))
    [dummy_graph.delete_vertex(v) for v in right_verts]
    comps = dummy_graph.connected_components() #should be one or two components now
    return first(comps, lambda x: myPath[0][0] in x)
    
#find number of faces to the left of a path in a planar graph
#myFaces is a list of pairs (face,face_vertices)
def num_left_faces(myGraph, myPath, myFaces,myEmbedding,n):
    if myPath == []:
        return 0
    left_verts = set(find_left_vertices(myGraph,myPath,myEmbedding,n))
    path_verts = [i[0] for i in myPath] + [myPath[-1][1]]
    counter = 0
    for face in myFaces: #check whether face is to the left
        if set(face[1])<=left_verts: #naive first check
            #could be that the vertices of the face all lie on the path, while the face lies to the right of the path, need to eliminate this case
            if not set(face[1]) <= set(path_verts):
                counter = counter + 1
            else:
                edges = edges_from_face(myGraph,face[0])
                face_is_good = True
                for edge in edges: #check whether the edge is to the right or left, meaning whether it is clockwise or counterclockwise from the source
                    initial = edge[0] #beginning of the edge
                    ending = edge[1]
                    n_ordered = myEmbedding[initial]
                    prev = n_ordered.index(path_verts[path_verts.index(initial)-1]) #should be okay since initial and edge should never be sources or sinks
                    next_ = n_ordered.index(path_verts[path_verts.index(initial)+1])
                    #left is all vertices from prev to next
                    if prev < next_ and ending in n_ordered[prev:next_]: 
                        face_is_good = False
                    elif next_ < prev and ending not in n_ordered[next_+1:prev-1]: 
                        face_is_good = False
                if face_is_good:
                    counter = counter + 1
    return counter
    
#find the degree of a flow in a planar graph
#the flow is given by the sum of the number of faces to the left of each path in the flow
def flow_degree(myGraph, myFlow,myFaces,myEmbedding,n):
    counter = 0
    for myPath in myFlow:
        counter = counter + num_left_faces(myGraph,myPath,myFaces,myEmbedding,n)
    return counter
    
#find flows from source set (1,2,...,n) to target set, which is a sorted list of size n of integers between 1 and 2n
#a flow is a vertex-disjoitn set of paths
def find_flow(myGraph,targets,myEmbedding,n):
    #print targets bad flow (1,7,8,9,10 
    myFlow = []
    sources = [str(p) for p in range(n,0,-1)]
    source_counter = 0
    used_verts = []
    for target in targets:
        if target in [str(p) for p in range(1,n+1)]: #in this case, we contribute only the empty path to the flow
            myFlow.append([]) #empty path
            used_verts.append(target)
            sources.remove(target)
        else:
            #source vertices only have one outgoing edge, so we can skip that iterations
            prev = sources[source_counter]
            current = myGraph.neighbors_out(prev)[0]
            path = [(prev,current)]
            used_verts.append(prev)
            used_verts.append(current)
            source_counter = source_counter + 1
            #find path from source to target
            while current != target:
                n_out = myGraph.neighbors_out(current)
                n_ordered = myEmbedding[current][::-1] #look for next neighbor clockwise from the previous
                found_next = False;
                counter = n_ordered.index(prev)+1
                num_neighbors = len(n_ordered)
                while found_next == False:
                    guess = n_ordered[counter%num_neighbors]
                    if counter == 2*num_neighbors+1: #we've seen all neighbors of current, and can't go to any of them, so backtrack
                        used_verts.append(current)
                        prev_edge = path[-2] #index should never be out of range unless something goes wrong
                        prev = prev_edge[0]
                        current = prev_edge[1]
                        path = path[:-1]
                        found_next = True
                    elif (len(guess) == 1 and guess != target) or guess not in n_out or guess in used_verts: #bad guess, go to next iteration
                        counter = counter + 1
                    elif guess in n_out and guess not in used_verts: #good guess, make an update and exit the loop
                        path.append((current,guess))
                        prev = current
                        current = guess
                        used_verts.append(current)
                        found_next = True
                    else:
                        print("error: I shouldn't be here")# something went wrong finding the flow
            #now I have found a path from source to target
            myFlow.append(path)
            #flow should have n paths now
    return myFlow
        
#we assume sources are 1,...,n and target set is given I
#flow polynomial is sum over all flows from [k] to I of weight of flow
def find_flow_poly(myGraph,myEmbedding, myFaces,I,n):
    sources = [str(p) for p in range(1,n+1)]
    sinks = I
    flows = map(lambda x:list(x),myGraph.flow_polytope(edges=myGraph.edges(),ends = (sources,sinks)).vertices()) #list of vertices of flow polytope, flows are not necessarily vertex-disjoint
    v_disj_flows = list(filter(lambda x:reduce(lambda w,z:w and z,map(lambda y:y<=1,x)),flows)) #list of vertex disjoint flows
    flow_weights = [] #list of exponent vectors for monomial of length F(G) number of faces of G
    for flow in v_disj_flows:
        #convert flow to list of paths, flow is a list of 0s/1s corresponding to whether a certain edge of the graph is present
        myEdges = [a[:2] for a in myGraph.edges()]
        flow_edges = []
        for i in range(len(myEdges)):
            if flow[i]==1:
                flow_edges.append(myEdges[i])
        flow_paths = []
        for source in sources:
            path = []
            current = source
            #if current is also a sink, then do nothing 
            while current not in I:
                #find next edge, there is a unique edge from current since the flow is vertex disjoint
                next_edge = first(flow_edges, lambda x:x[0]==current)
                current = next_edge[1]
                path.append(next_edge)
            flow_paths.append(path)
        flow_weight = [0]*len(myFaces)
        for path in flow_paths:
            left_faces = find_left_faces(myGraph,path,myFaces,myEmbedding,n)
            for face in left_faces:
                flow_weight[myFaces.index(face)] = flow_weight[myFaces.index(face)] + 1
        flow_weights.append(flow_weight)
        #flow paths is a list of paths in the flow, now we need to find the weight of the flow
        #the weight is the sum over paths in the flow of the weight of each path
        #the weight of a path is the list of faces to its left
    return flow_weights
        
        
#return list of faces to the left of a path in a planar graph
#myFaces is a list of pairs (face,face_vertices)
def find_left_faces(myGraph, myPath, myFaces,myEmbedding,n):
    if myPath == []:
        return []
    left_faces = []
    left_verts = set(find_left_vertices(myGraph,myPath,myEmbedding,n))
    path_verts = [i[0] for i in myPath] + [myPath[-1][1]]
    for face in myFaces: #check whether face is to the left
        if set(face[1])<=left_verts: #naive first check
            #could be that the vertices of the face all lie on the path, while the face lies to the right of the path, need to eliminate this case
            if set(face[1]).intersection(set([str(p) for p in range(1,2*n+1)])) != set():
                if set(face[1]).intersection(set([str(p) for p in range(1,2*n+1)])) != set([1,2*n]):
                    left_faces.append(face)
                #now the face does have vertices 1,2n
                else:
                    if myPath[0][0] in set([str(p) for p in range(n+1,2*n+1)]):
                        left_faces.append(face)
            elif not set(face[1]) <= set(path_verts): #face is to the left
                left_faces.append(face)
            else: #now face is a subset of the path, and there should be a unique edge in the face not in the path
                edges = edges_from_face(myGraph,face[0])
                face_is_good = True
                for edge in edges: #check whether the edge is to the right or left, meaning whether it is clockwise or counterclockwise from the source
                    initial = edge[0] #beginning of the edge
                    ending = edge[1]
                    n_ordered = myEmbedding[initial]
                    prev = n_ordered.index(path_verts[path_verts.index(initial)-1]) #should be okay since initial and edge should never be sources or sinks
                    next_ = n_ordered.index(path_verts[path_verts.index(initial)+1])
                    #left is all vertices from prev to next
                    if prev < next_ and ending in n_ordered[prev:next_]: 
                        face_is_good = False
                    elif next_ < prev and ending not in n_ordered[next_+1:prev-1]: 
                        face_is_good = False
                if face_is_good:
                    left_faces.append(face)
    return left_faces

#print out a list of valuations of flow polynomials in polymake format to determine volume and f-vector, etc of flow polytope
def all_flow_polys(myGraph,n):
    [myGraph.add_edge((str(i),str(i+1))) for i in range(1,2*n)]
    myGraph.add_edge((str(2*n),str(1)))
    myGraph.is_circular_planar(set_embedding=True, boundary = [str(p) for p in range(1,2*n+1)], ordered = True)
    #there are two reasonable ways for the graph to be embedded: either with the labels 1,..,2n in clockwise or counterclockwise order
    faces = myGraph.faces()
    outer_face = first(faces, lambda x: set(flatten(x)) == set([str(p) for p in range(1,2*n+1)]))
    outer_face_verts = list(flatten(outer_face))
    one_index = outer_face_verts.index('1')
    emb = None
    if outer_face_verts[(one_index+1)%(2*n)]=='2': #embedding is mirror of what I want
        emb = dict([(akey,avalue[::-1]) for akey,avalue in myGraph.get_embedding().items()]) #boundary vertices counterclockwise
    else: #embedding is what I want
        emb = myGraph.get_embedding() #clockwise order
    faces.remove(outer_face)
    faces_verts = [(face,[i[0] for i in face]) for face in faces] #list of pairs: (face,face vertices)
    [myGraph.delete_edge((str(i),str(i+1))) for i in range(1,2*n)]
    myGraph.delete_edge((str(2*n),'1'))
    face_labels = label_faces(myGraph,emb,faces_verts,n)
    targets = list(combinations([str(p) for p in range(1,2*n+1)],n))
    order = coord_vec(face_labels, faces_verts,n)
    new_order = [i[::-1] for i in sorted([i[::-1] for i in order])][::-1]
    shifter = [new_order.index(i) for i in order]
    #mat = toGT(new_order,n)
    #print("$m = new Matrix<Rational>("+str(mat)+");)
    flow_polynomials = tuple([tuple(sorted(map(lambda x:new_vec(face_labels, faces_verts,x,n), find_flow_poly(myGraph, emb, faces_verts,target,n)))[0]) for target in targets])
    flow_polys_ordered = tuple([tuple([poly[shifter.index(i)] for i in range(len(shifter))]) for poly in flow_polynomials])
    print("$p = new Polytope<Rational>(POINTS=>"+str([[1]+list(x)[1:] for x in flow_polys_ordered])+"); print $p->F_VECTOR; print \"\\n\"; print $p->LATTICE_VOLUME;")
    return
    
#return a list of flow polynomials (in lexicographic order) for Grassmannian (n,2n)
def all_flow_polys_nonsym(myGraph,n):
    [myGraph.add_edge((str(i),str(i+1))) for i in range(1,2*n)]
    myGraph.add_edge((str(2*n),'1'))
    myGraph.is_circular_planar(set_embedding=True, boundary = [str(p) for p in range(1,2*n+1)], ordered = True)
    #there are two reasonable ways for the graph to be embedded: either with the labels 1,..,2n in clockwise or counterclockwise order
    faces = myGraph.faces()
    outer_face = first(faces, lambda x: set(flatten(x)) == set([str(p) for p in range(1,2*n+1)]))
    outer_face_verts = list(flatten(outer_face))
    one_index = outer_face_verts.index('1')
    emb = None
    if outer_face_verts[(one_index+1)%(2*n)]=='2': #embedding is mirror of what I want
        emb = dict([(akey,avalue[::-1]) for akey,avalue in myGraph.get_embedding().items()]) #boundary vertices counterclockwise
    else: #embedding is what I want
        emb = myGraph.get_embedding() #clockwise order
    faces.remove(outer_face)
    faces_verts = [(face,[i[0] for i in face]) for face in faces] #list of pairs: (face,face vertices)
    [myGraph.delete_edge((str(i),str(i+1))) for i in range(1,2*n)]
    myGraph.delete_edge((str(2*n),'1'))
    face_labels = label_faces(myGraph,emb,faces_verts,n)
    targets = list(combinations([str(p) for p in range(1,2*n+1)],n))
    #lg_labels = coord_vec(face_labels, faces_verts,n)
    #lg_coords = [i[::-1] for i in sorted([i[::-1] for i in lg_labels])][::-1]
    old_order = [{v:k for k,v in face_labels.items()}[tuple(x[1])] for x in faces_verts]
    new_order = [i[::-1] for i in sorted([i[::-1] for i in old_order])][::-1]
    #mat = toLGr(new_order,lg_coords,n)
    #print("$A = new Matrix<Rational>("+str(mat)+");)"
    '''
    leq = lambda a,b:reduce(lambda x,y:x and y, [a[i]>=b[i] for i in range(len(a))])
    compute the stanley triangulation from linear extensions
    P = Poset([new_order[1:],leq])
    lxts = list(P.linear_extensions())
    positive = [[0]+[1]+[0]*(len(new_order)-2)]
    bounded = [[1]+[0]*(len(new_order)-2)+[-1]]
    simplices = []
    j=0
    for lxt in lxts:
        temp = []
        for i in range(len(lxt)-1):
            row = [0]*len(new_order)
            row[new_order.index(lxt[i+1])]=1
            row[new_order.index(lxt[i])]=-1
            temp.append(row)
        temp = positive + temp + bounded
        simplices.append("$q"+str(j)+" = new Polytope<Rational>(INEQUALITIES=>"+str(temp)+");")
        j = j+1
    mat = toGT(new_order,n)
    print("$m = new Matrix<Rational>("+str(mat)+");)
    '''
    shifter = [new_order.index(i) for i in old_order]
    flow_polynomials = tuple([tuple(sorted(find_flow_poly(myGraph, emb, faces_verts,target,n))[0]) for target in targets])
    flow_polys_ordered = tuple([tuple([poly[shifter.index(i)] for i in range(len(shifter))]) for poly in flow_polynomials])
    print("$p = new Polytope<Rational>(POINTS=>"+str([[1]+list(x)[1:] for x in set(flow_polys_ordered)])+"); print $p->F_VECTOR; print \"\\n\"; print $p->LATTICE_VOLUME;")
    return
    #return simplices

#output the linear transformation (in polymake format) sending the grassmannian polytopes to the lagrangian grassmannian polytopes
#this needs fixing
def toLGr(grlabels,lglabels,n):
    mat = []
    length = len(grlabels)
    mat.append([1]+[0]*(length-1))
    for label in lglabels[1:]:
        temp_row=[0]*length
        temp_row[grlabels.index(label)]=1
        transp_part = ''.join(sorted(list(set([str(j) for j in range(1,2*n+1)]).difference(set([str(2*n+1-int(i)) for i in label])))))
        temp_row[grlabels.index(transp_part)]=1
        mat.append(temp_row)
    return map(list,zip(*mat))
    
#output the linear transformation (in polymake format) sending the superpotential polytope/newton okounkov body to the gelfand tsetlin polytope (in the rectangles cluster only for the Grassmannian)
#I'll write a separate one later for the lagrangian Grassmannian
def toGT(labels,n):
    #My coordinates are n element subsets of [2n], ordered from right to left by largest element first
    #i.e. 34 < 24 < 14 < 23 < 12
    mat = []
    length = len(labels)
    mat.append([1]+[0]*(length-1))
    for label in labels[1:]:
        temp_row = [0]*length
        temp_row[labels.index(label)]=1
        if not(label[0]==str(n) or label[1]==str(n+2)):
            #label comes in two chunks because rectangles cluster
            #both chunks are "continuous" the label looks like (i)(i+1)...(i+a) (j)(j+1)...(j+b)
            temp = [int(label[i+1])-int(label[i])>1 for i in range(n-1)]
            try:
                #find the beginning of the second chunk
                first = ''.join(map(lambda x:str(int(x)+1),label[:temp.index(True)+1]))[:-1]
                last = label[temp.index(True)+1:]
                last = str(int(last[0])-1)+last
                label = first+last
            except ValueError:
                #only one chunk, which is okay it just means a maximally long thing
                label = ''.join(map(lambda x:str(int(x)+1),label))[:-1]+str(2*n)
            temp_row[labels.index(label)]=-1
        mat.append(temp_row)
    return map(list, zip(*mat))
    
def coord_vec(labels,myFaces,n):
    to_remove = []
    temp = [{v:k for k,v in labels.items()}[tuple(x[1])] for x in myFaces]
    for rel in rels(n):
        try:
            ind_1 = myFaces.index(first(myFaces, lambda x:set(tuple(x[1]))==set(labels[rel[0]])))
            ind_2 = myFaces.index(first(myFaces, lambda x:set(tuple(x[1]))==set(labels[rel[1]])))
            to_remove.append(ind_2)
        except KeyError:
            #face wasn't in graph, this isn't a problem, just move on
            pass
    for x in sorted(to_remove)[::-1]:
        del temp[x]
    return temp
    
def new_vec(labels,myFaces,vec,n):
    to_remove = []
    for rel in rels(n):
        try:
            ind_1 = myFaces.index(first(myFaces, lambda x:set(tuple(x[1]))==set(labels[rel[0]])))
            ind_2 = myFaces.index(first(myFaces, lambda x:set(tuple(x[1]))==set(labels[rel[1]])))
            to_remove.append(ind_2)
            vec[ind_1] = vec[ind_1]+vec[ind_2]
        except KeyError:
            #face wasn't in graph, this isn't a problem, just move on
            pass
    for x in sorted(to_remove)[::-1]:
        del vec[x]
    return vec
    
#label faces of plabic graph by trip labelling using source convention
#so faces to left of trip starting at vertex i get label i    
#at this point, we are working with full plabic graph (with boundary disk)
def label_faces(myGraph,myEmbedding,myFaces,n):
    trips = []
    tempGraph = myGraph.copy()
    [tempGraph.delete_edge((str(i),str(i+1))) for i in range(1,2*n)]
    tempGraph.delete_edge((str(2*n),str(1)))
    #find trips in tempGraph to avoid edges between boundary vertices
    for i in range(1,2*n+1):
        prev = str(i)
        current = tempGraph.neighbors(prev)[0]
        path = [(prev,current)]
        while current[0] in {'b','w'}:
            n_ordered = None
            if current[0]=='b': #turn maximally right
                n_ordered = myEmbedding[current] #look clockwise/right
            elif current[0]=='w': #turn maximally left    
                n_ordered = myEmbedding[current][::-1] #look counterclockwise/left
            next_ = n_ordered[(n_ordered.index(prev)+1)%len(n_ordered)]
            path.append((current,next_))
            prev = current
            current = next_
        #path should now go from boundary vertex to boundary vertex following the rules of the road, i.e. a trip
        trips.append(path)
    #now go back to using myGraph to get faces correctly
    trips_left_faces = [[set(x[1]) for x in find_left_faces(myGraph,trip,myFaces,myEmbedding,n)] for trip in trips]
    labels = {tuple(face[1]):reduce(lambda x,y:str(x)+str(y),filter(lambda x:set(face[1]) in trips_left_faces[x-1],range(1,2*n+1))) for face in myFaces}
    return {v:k for k,v in labels.items()}
    
def rels(n):
    pluckers = [tuple(i) for i in combinations(range(1,2*n+1),n)]
    idents = [tuple(sorted(set(range(1,2*n+1)).difference(map(lambda x:2*n+1-x,i)))) for i in pluckers]
    pluckers = map(lambda x:reduce(lambda y,z:str(y)+str(z),x),pluckers)
    idents = map(lambda x:reduce(lambda y,z:str(y)+str(z),x),idents)
    return list(set(filter(lambda x:x[0]!=x[1],[tuple(sorted(x)) for x in zip(pluckers,idents)])))
    
#find weight vectors for graph
def find_vector(myGraph, n):
    myGraph.is_circular_planar(set_embedding=True, boundary = [str(p) for p in range(1,2*n+1)], ordered = True)
    #there are two reasonable ways for the graph to be embedded: either with the labels 1,..,2n in clockwise or counterclockwise order
    faces = myGraph.faces()
    max_face_verts = list(OrderedDict.fromkeys(filter(lambda x:len(x)==1,flatten(sorted(faces,key=lambda x:len(x))[-1]))))
    one_index = max_face_verts.index("1")
    emb = None
    if max_face_verts[(one_index+1)%(2*n)]=='2': #embedding is mirror of what I want
        emb = dict([(akey,avalue[::-1]) for akey,avalue in myGraph.get_embedding().items()]) #boundary vertices counterclockwise
    else: #embedding is what I want
        emb = myGraph.get_embedding() #clockwise order
    faces = filter(lambda x:set(flatten(x)).intersection(set([str(p) for p in range(1,2*n+1)])) == set(),faces)
    faces_verts = [(face,[i[0] for i in face]) for face in faces] #list of pairs: (face,face vertices)
    targets = list(combinations([str(p) for p in range(1,2*n+1)],n))
    degrees = tuple([flow_degree(myGraph, find_flow(myGraph,target,emb,n),faces_verts,emb,n) for target in targets])
    return degrees
    
#input starting plabic graph, and explore the weight vectors obtainable by mutation
def tropical_traverse_sym(startingGraph,n):
    vectors = defaultdict(int)
    my_graphs = []
    working_graphs = [(startingGraph,1)]
    done = False
    i=1
    while working_graphs:
        stdout.write("\rComputing graph %i" % i)
        stdout.flush()
        current = working_graphs.pop(0)
        #current[0].show(figsize=[10,10])
        vector = find_vector(current[0],n)
        i = i + 1
        if vectors[vector] == 0: #new vector, and new plabic graph (I'm assuming a bijection between plabic graphs and cones)
            vectors[vector] = current[1]
            my_graphs.append((current[0].copy(),current[1]))
            faces = find_sym_squares(current[0])
            for face in faces:
                temp_copy = current[0].copy()
                sym_sq_move(temp_copy,face,n)
                working_graphs.append((temp_copy,current[1]+1))
        else:
            vectors[vector] = min(vectors[vector], current[1])
        working_graphs = sorted(working_graphs,key=lambda x:x[1])
    print('\n')
    return vectors,my_graphs
