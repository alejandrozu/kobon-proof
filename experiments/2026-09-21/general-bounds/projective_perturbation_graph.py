"""Conflict graph relaxation for perturbing the concurrent projective FP family.

Modular labels identify concurrent triples exactly. Face order and local sector
colors use floating trigonometry. MILP optima are exploratory solver evidence,
not exact geometry or kernel certificates. No realizability conclusion follows.
"""
import argparse,collections,itertools,json,math,sys,time
from pathlib import Path
import numpy as np
from concurrent_fp_charts import projective
ROOT=Path(__file__).resolve().parents[3]
sys.path.insert(0,str(ROOT/'work/general-bounds-deps'))
from scipy.optimize import milp,LinearConstraint,Bounds
from scipy.sparse import lil_matrix

def analyze(n,seconds=120):
    xyz,fi,fs,keys,gap=projective(n);xy=xyz[:,:2]/xyz[:,2,None]
    incident=collections.defaultdict(list)
    for a,face in enumerate(fi):
        for k,p in enumerate(face):
            if len(keys[p])!=3:continue
            rays=[]
            for j in keys[p]:
                theta=j*math.pi/n
                rays.extend(((-theta)%(2*math.pi),(math.pi-theta)%(2*math.pi)))
            rays.sort();others=[j for j in range(3)if j!=k]
            dirs=[]
            for j in others:
                q=face[j];d=(xyz[q,:2]-xy[p]*xyz[q,2])*(fs[a,j]*fs[a,k])
                dirs.append(d/np.linalg.norm(d))
            mid=dirs[0]+dirs[1];angle=math.atan2(mid[1],mid[0])%(2*math.pi)
            color=int(np.searchsorted(rays,angle)%6%2)
            incident[p].append((a,color))
    edges=set()
    for vals in incident.values():
        for (a,c),(b,d)in itertools.combinations(vals,2):
            if c!=d:edges.add(tuple(sorted((a,b))))
    A=lil_matrix((len(edges),len(fi)))
    for r,(a,b)in enumerate(sorted(edges)):A[r,a]=A[r,b]=1
    start=time.monotonic()
    ans=milp(-np.ones(len(fi)),integrality=np.ones(len(fi)),bounds=Bounds(0,1),
             constraints=LinearConstraint(A.tocsr(),-np.inf,1),options={'time_limit':seconds,'mip_rel_gap':0})
    selected=[]if ans.x is None else np.flatnonzero(ans.x>.5).tolist()
    assert all(not(a in selected and b in selected)for a,b in edges)
    q=sum(len(k)==3 for k in keys)
    return dict(n=n,projective_old_triangles=len(fi),triple_points=q,conflict_edges=len(edges),
                independent_size=len(selected),perturbation_relaxed_lower=q+len(selected),
                independent_upper=None if not hasattr(ans,'mip_dual_bound')else -float(ans.mip_dual_bound),
                milp_status=int(ans.status),message=str(ans.message),seconds=time.monotonic()-start,
                selected_faces=[fi[a].tolist()for a in selected],
                limitations='floating face order/colors and external MILP solver; no straight-line realization or exact upper proof')

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--ns',default='9,12,15,18,21,27,33,39,45,51')
    p.add_argument('--seconds',type=float,default=120);p.add_argument('--out',type=Path,required=True)
    a=p.parse_args();a.out.mkdir(parents=True,exist_ok=True)
    for n in map(int,a.ns.split(',')):
        row=analyze(n,a.seconds);(a.out/f'n{n:03d}.json').write_text(json.dumps(row,indent=2)+'\n')
        print(json.dumps({k:v for k,v in row.items()if k!='selected_faces'}),flush=True)
