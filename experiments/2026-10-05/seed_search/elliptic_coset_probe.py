"""Preliminary numerical probe of torsion cosets on two-component real cubics.

E:y²=(x-1)(x-s)(x+1). The second-component translation is the algebraic
two-torsion point(-1,0). A shifted cyclic coset has no prescribed triple
concurrences. Any higher count requires exact realization and a new theorem.
"""
from pathlib import Path
import sys,json,itertools as it,time,random,math
ROOT=Path(__file__).resolve().parents[3];sys.path.insert(0,str(ROOT/'work/construction-deps'))
import numpy as np
from scipy.special import ellipk,ellipj

def lines(n,s,phase,mixed):
    m=(s+1)/2;K=ellipk(m);out=[]
    for j in range(n):
        v=2*K*(j+phase)/n;sn,cn,dn,_=ellipj(v,m);x=-1+2/sn**2;y=-math.sqrt(8)*cn*dn/sn**3
        if mixed and j%2:x,y=(2*s+1-x)/(x+1),-2*(s+1)*y/(x+1)**2
        row=np.array([float(x+2),float(y+2),1.]);out.append(row/np.linalg.norm(row))
    return np.array(out)

def geometry(L):
    n=len(L);pairs=list(it.combinations(range(n),2));vertices=np.array([np.cross(L[i],L[j]) for i,j in pairs]);vertices=vertices/vertices[:,2,None];rows=[];edges={};adj=[set() for _ in pairs]
    for i in range(n):
        row=[k for k,pair in enumerate(pairs) if i in pair];axis=0 if abs(L[i,1])>1e-15 else 1;row.sort(key=lambda k:vertices[k,axis]);rows.append(row)
        for a,b in zip(row,row[1:]):e=tuple(sorted((a,b)));assert e not in edges;edges[e]=(i,0);adj[a].add(b);adj[b].add(a)
        a,b=row[-1],row[0];e=tuple(sorted((a,b)));assert e not in edges;edges[e]=(i,1);adj[a].add(b);adj[b].add(a)
    faces=[]
    for a in range(len(pairs)):
        for b,c in it.combinations(sorted(v for v in adj[a] if v>a),2):
            if c not in adj[b]:continue
            ab,ac,bc=[edges[tuple(sorted(e))] for e in [(a,b),(a,c),(b,c)]]
            if len({ab[0],ac[0],bc[0]})<3 or (ab[1]+ac[1]+bc[1])%2:continue
            faces.append(dict(vertices=[a,b,c],lift_signs=[1,-1 if ab[1] else 1,-1 if ac[1] else 1],wraps=ab[1]+ac[1]+bc[1]))
    return vertices,faces

def count(pole,vertices,faces):
    vals=vertices@pole
    if min(abs(vals))<1e-10:return None
    return int(sum(min(t['lift_signs'][j]*vals[v] for j,v in enumerate(t['vertices']))>0 or max(t['lift_signs'][j]*vals[v] for j,v in enumerate(t['vertices']))<0 for t in faces))

if __name__=='__main__':
    start=time.time();rng=np.random.default_rng(6924);records=[]
    for n,s,mixed in it.product([8,14,18,20,26,32,38,50,60],[-.8,0.,.8],[False,True]):
        L=lines(n,s,1/6,mixed);vertices,faces=geometry(L);best=count(np.array([0.,0.,1.]),vertices,faces);pole=[0,0,1]
        for p in rng.normal(size=(400,3)):
            t=count(p,vertices,faces)
            if t is not None and t>best:best=t;pole=list(map(float,p))
        G=n*(n-3)//3+1+n%2;r=dict(n=n,cubic_parameter=s,mixed_component=mixed,phase='1/6',projective_triangles=len(faces),default=sum(t['wraps']==0 for t in faces),best_chart=best,pole=pole,G=G,gain=best-G);records.append(r);print(json.dumps(r),flush=True)
    out=ROOT/'research/openmath-seven-hour-2026-10-05/seed_search/elliptic-cosets';out.mkdir(parents=True,exist_ok=True);(out/'report.json').write_text(json.dumps(dict(records=records,seconds=time.time()-start,status='Numerical screening only: no exact certificate, no new lower bound claimed'),indent=2)+'\n')
