"""Exploratory FP projective-infinity boundary saturation census.

The original infinity line has uniformly spaced direction intersections. After
the coordinate change (X,Y,Z)->(X,Z,Y+beta Z), it becomes finite y=0 and has
intercepts -cot(theta). A second mode uses the BBL integer tangent grid with
the pole omitted and its central point split. Counts here are floating point;
they are negative diagnostics, not upper proofs or algebraic certificates.
"""
import json,math
from pathlib import Path
import numpy as np

def triangles(ls):
    n=len(ls);a,b,c=ls.T
    den=a[:,None]*b[None,:]-b[:,None]*a[None,:];np.fill_diagonal(den,1)
    if np.min(np.abs(den))<1e-12:return None
    x=(c[:,None]*b[None,:]-b[:,None]*c[None,:])/den
    y=(a[:,None]*c[None,:]-c[:,None]*a[None,:])/den
    u=b[:,None]*x-a[:,None]*y;np.fill_diagonal(u,np.inf)
    rows=np.argsort(u,axis=1)[:,:-1]
    tri=np.stack((np.repeat(np.arange(n),n-1),rows.ravel(),np.roll(rows,-1,axis=1).ravel()),axis=1)
    tri.sort(axis=1);keys=tri[:,0]*n*n+tri[:,1]*n+tri[:,2]
    unique,inv,ct=np.unique(keys,return_inverse=True,return_counts=True)
    wr=np.zeros((n,n-1));wr[:,-1]=1
    parity=np.bincount(inv,weights=wr.ravel()).astype(int)%2
    keys=unique[(ct==3)&(parity==0)]
    return [(int(k//(n*n)),int(k//n%n),int(k%n))for k in keys]

def family(q,phase,split=False):
    if split:
        theta=np.array([i*math.pi/q for i in range(1,q)if i!=q//2]+[math.pi/2-1e-5,math.pi/2+1e-5])
    else:theta=(np.arange(q)+.5)*math.pi/q
    a=np.sin(theta);b=np.cos(theta);c=np.sin(3*theta+phase)
    old=np.column_stack((a,-c-.517*b,-b))
    return np.vstack(((0,1,0),old))

if __name__=='__main__':
    out=Path(__file__).resolve().with_name('fp-boundary-grid.json');rows=[]
    for q in range(4,102,2):
        for split in (False,True):
            vals=[]
            for phase in np.linspace(0,math.pi,65,endpoint=False):
                ts=triangles(family(q,phase,split))
                if ts is None:continue
                vals.append(dict(phase=float(phase),projective=len(ts),boundary=sum(0 in t for t in ts)))
            best=max(vals,key=lambda v:(v['boundary'],v['projective']))
            row=dict(q=q,split=split,required_saturation=q-1,best=best)
            rows.append(row);print(json.dumps(row),flush=True)
    out.write_text(json.dumps(dict(results=rows,limitations='Floating geometric census only; no impossibility proof; local singular phases may need symbolic treatment.'),indent=2)+'\n')
