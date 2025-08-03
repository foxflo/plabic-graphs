import cvxopt as co
import numpy as np

#the tropical lagrangian grassmannian Trop(LGr(3,6)) is a polyhedral fan consisting of 35 rays and 159 3-dimensional cones
#each cone contains 7 rays, but the tropical variety has a four dimensional lineality space, so we only list the 3 unique rays per cone below
raysInCones = [[0,1,5],[1,2,7],[1,3,8],[0,1,11],[0,1,12],[1,2,11],[1,3,12],[1,2,13],[1,3,13],[0,4,5],[1,5,6],[1,6,7],[1,6,8],[2,7,9],[3,8,10],[1,5,14],[1,7,15],[1,8,16],[0,4,17],[2,9,18],[3,10,19],[1,11,16],[1,12,15],[1,13,14],[0,5,20],[4,5,6],[1,14,15],[1,14,16],[1,15,16],[6,7,9],[2,7,24],[6,8,10],[3,8,23],[0,11,17],[0,12,17],[2,11,18],[3,12,19],[2,13,18],[3,13,19],[0,11,20],[0,12,20],[2,11,24],[3,12,23],[2,13,24],[3,13,23],[4,5,14],[7,9,15],[8,10,16],[5,6,20],[6,7,24],[6,8,23],[4,6,27],[4,6,28],[6,9,26],[6,10,26],[6,9,27],[6,10,28],[5,14,20],[14,15,16],[7,15,24],[8,16,23],[11,17,18],[12,17,19],[13,18,19],[4,14,27],[4,14,28],[9,15,26],[10,16,26],[9,15,27],[10,16,28],[6,20,23],[6,20,24],[14,15,22],[14,16,21],[6,23,24],[15,16,25],[4,17,27],[4,17,28],[17,18,19],[9,18,26],[10,19,26],[9,18,27],[10,19,28],[11,20,24],[6,20,26],[12,20,23],[6,23,27],[14,15,27],[6,24,28],[14,16,28],[13,23,24],[15,16,26],[14,20,21],[14,20,22],[16,21,23],[15,22,24],[15,24,25],[16,23,25],[18,19,26],[17,18,27],[17,19,28],[11,16,29],[12,15,30],[13,14,31],[13,14,32],[12,15,33],[11,16,34],[20,21,23],[20,22,24],[20,23,24],[23,24,25],[11,18,29],[12,19,30],[13,18,31],[13,19,32],[12,17,33],[11,17,34],[11,20,29],[12,20,30],[13,23,31],[13,24,32],[12,23,33],[11,24,34],[14,21,31],[16,21,29],[14,22,32],[15,22,30],[15,25,33],[16,25,34],[16,26,29],[15,26,30],[14,27,31],[14,28,32],[15,27,33],[16,28,34],[20,21,29],[20,22,30],[21,23,31],[22,24,32],[23,25,33],[24,25,34],[18,26,29],[19,26,30],[18,27,31],[19,28,32],[17,27,33],[17,28,34],[20,26,29],[20,26,30],[23,27,31],[24,28,32],[23,27,33],[24,28,34],[18,29,31],[19,30,32],[17,33,34],[21,29,31],[22,30,32],[25,33,34]]

rayLabels = ['B', 'p', 'B', 'B', 'B', 'C', 'p', 'C', 'C', 'B', 'B', 'a', 'a', 'a', 'p', 'p', 'p', 'A', 'A', 'A', 'p', 'C', 'C', 'p', 'p', 'C', 'a', 'a', 'a', 'B', 'B', 'B', 'B', 'B', 'B']
coneLabeler = dict(zip([i for i in range(35)],rayLabels))
coneLabels = [[coneLabeller[i] for i in cone] for cone in raysInCones]

#rays of cone as list of lists, vector in same vector space as list, dimension of lineality space (last n entries)
#output whether vector is in cone given by rays
def formlp(rays,vect,lineality):
    numRays = len(rays)
    print(rays)
    A = co.matrix(rays)
    A = np.vstack((np.array(A),-np.array(A)))
    for i in range(numRays-lineality):
        a = np.zeros((numRays,))
        a[i] = -1.
        A = np.vstack((A,a))
    
    b = co.matrix(vect)
    b = np.vstack((np.array(b),-np.array(b)))
    b = np.vstack((b,np.zeros((numRays-lineality,))[:,np.newaxis]))
    
    c = np.zeros((numRays,))
    co.solvers.options['show_progress']=False
    return co.solvers.lp(co.matrix(c),co.matrix(A),co.matrix(b))

#figure out which cone contains given vector
#coneFile is file containing list of cones, where each cone is represented by a list of rays that span it
def runlps(vector,coneFile,lineality):
    coneData = __import__(coneFile)
    procVec = map(lambda x:float(x),vector)
    containingCones = []
    for i in range(len(coneData.cones)):
        procCone = [list(map(lambda x:float(x),ray)) for ray in coneData.cones[i]]
        sol = formlp(procCone,vector,lineality)
        if sol['status']=='optimal':
            containingCones = containingCones + [(coneLabels[i],raysInCones[i])]
    return containingCones
    
weights = [[0,0,0,0,0,0,1,2,0,1,1,2,3,5],[0,0,0,1,0,1,3,3,2,3,3,3,3,7],[0,0,0,0,0,0,1,3,0,1,1,3,4,5],[0,0,0,2,0,2,3,3,3,3,3,3,3,7],[0,0,1,1,1,1,1,4,1,1,1,4,5,5],[0,0,0,1,0,1,1,4,2,2,3,4,4,5],[0,0,1,3,2,3,3,4,3,3,3,4,5,7],[0,0,0,3,0,3,3,4,4,4,4,4,4,7],[0,0,1,2,1,2,1,5,3,2,3,5,5,5],[0,0,1,4,2,4,3,5,4,4,4,5,6,7],[0,0,1,3,1,3,1,5,4,3,4,5,5,5],[0,0,2,4,3,4,3,6,4,4,4,6,7,7]]

cones = []
for weight in weights:
    cones = cones + [runlps([-i for i in weight],"cones",4)]
print(cones)
