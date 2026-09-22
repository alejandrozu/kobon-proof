"""Exploratory line families dual to real elliptic-curve torsion cosets.

Both real components are sampled for even orders. Numerical scans are not
proofs; any reported improvement is separately rounded and exactly checked.
"""
from __future__ import annotations
import argparse, json, math, sys
from pathlib import Path
from fractions import Fraction
import numpy as np

ROOT=Path(__file__).resolve().parents[3]
sys.path.insert(0,str(ROOT/'work/general-bounds-deps'))
sys.path.insert(0,str(ROOT/'research/kobon-extension'))
from scipy.special import ellipj,ellipk
from exact_geometry import arrangement,primitive

def curve(n,modulus,phase,two=True):
    # e1-e3 = 1, e2-e3 = modulus, e1+e2+e3=0.
    e3=-(1+modulus)/3
    u=2*ellipk(modulus)*(np.arange(n)+phase)/n
    sn,cn,dn,_=ellipj(u,modulus)
    x=e3+1/sn**2
    y=-2*cn*dn/sn**3
    if two:
        mask=(np.arange(n)%2)==1
        x[mask]=e3+modulus*sn[mask]**2
        y[mask]=2*modulus*sn[mask]*cn[mask]*dn[mask]
    result=np.column_stack((x,y,np.ones(n)))
    return result/np.linalg.norm(result,axis=1)[:,None]

def score(lines,projective=False):
    n=len(lines)
    a,b,c=lines.T
    det=a[:,None]*b[None,:]-b[:,None]*a[None,:]
    det2=det+np.eye(n)
    if np.min(np.abs(det2))<1e-12:return None
    x=(c[:,None]*b[None,:]-b[:,None]*c[None,:])/det2
    y=(a[:,None]*c[None,:]-c[:,None]*a[None,:])/det2
    u=b[:,None]*x-a[:,None]*y
    np.fill_diagonal(u,np.inf)
    rows=np.argsort(u,axis=1)[:,:-1]
    if projective:
        aa=np.broadcast_to(np.arange(n)[:,None],(n,n-1)).ravel()
        bb=rows.ravel();cc=np.roll(rows,-1,axis=1).ravel()
        wraps=np.zeros((n,n-1),dtype=np.int8);wraps[:,-1]=1;wraps=wraps.ravel()
    else:
        aa=np.broadcast_to(np.arange(n)[:,None],(n,n-2)).ravel()
        bb=rows[:,:-1].ravel();cc=rows[:,1:].ravel()
    triples=np.stack((aa,bb,cc),axis=1)
    triples.sort(axis=1)
    keys=triples[:,0]*n*n+triples[:,1]*n+triples[:,2]
    _,inverse,counts=np.unique(keys,return_inverse=True,return_counts=True)
    if projective:
        parities=np.bincount(inverse,weights=wraps).astype(int)%2
        return int(np.count_nonzero((counts==3)&(parities==0)))
    return int(np.count_nonzero(counts==3))

def certify(lines,path,expected,metadata):
    for digits in (10,14,17):
        denom=10**digits
        ls=[primitive([Fraction(round(float(x)*denom),denom)for x in l])for l in lines]
        ar=arrangement(ls)
        count=len(ar['triangles'])
        simple=all(len(v)==2 for v in ar['points'].values())
        if count==expected and simple:
            data=dict(n=len(ls),triangle_count=count,simple=simple,
                      lines_frac=[[str(x)for x in l]for l in ls],
                      method='rational rounding of elliptic-curve torsion coset dual',
                      verification='exact adjacency; direct-sign check pending',**metadata)
            path.write_text(json.dumps(data,indent=2)+'\n')
            return
    raise RuntimeError((expected,count))

if __name__=='__main__':
    p=argparse.ArgumentParser()
    p.add_argument('--max-n',type=int,default=100)
    p.add_argument('--out',type=Path,required=True)
    args=p.parse_args()
    args.out.mkdir(parents=True,exist_ok=True)
    report=[]
    for n in range(4,args.max_n+1,2):
        trials=[]
        for modulus in (.01,.1,.3,.5,.7,.9,.99):
            for phase in (1/12,1/6,1/4,5/12,1/2,7/12,3/4,5/6,11/12):
                lines=curve(n,modulus,phase)
                t=score(lines)
                trials.append(dict(modulus=modulus,phase=phase,triangles=t))
        best=max((t for t in trials if t['triangles']is not None),key=lambda t:t['triangles'])
        baseline=n*(n-3)//3+1
        if best['triangles']>baseline:
            lines=curve(n,best['modulus'],best['phase'])
            certify(lines,args.out/f'n{n:03d}.json',best['triangles'],best)
        row=dict(n=n,best=best,baseline=baseline,trials=trials)
        report.append(row)
        print(json.dumps({k:v for k,v in row.items()if k!='trials'}),flush=True)
    (args.out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
