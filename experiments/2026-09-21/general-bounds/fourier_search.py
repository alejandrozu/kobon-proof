"""Structured support-function search beyond the cubic family.

Line normals are equally spaced; offsets contain odd Fourier harmonics 3..H.
This changes the projective topology through global, correlated deformations.
Floating proposals are rationalized and affine-counted exactly before saving.
"""
import argparse,json,math,time
from pathlib import Path
import numpy as np
from elliptic_scan import certify,score as line_score

def run(n,seconds,seed,out,H=15):
    out.mkdir(parents=True,exist_ok=True);rng=np.random.default_rng(seed)
    theta=(np.arange(n)+.5)*math.pi/n
    delta=theta[None,:]-theta[:,None];np.fill_diagonal(delta,math.pi/2)
    A=1/np.sin(delta);B=np.cos(delta)*A
    np.fill_diagonal(A,0);np.fill_diagonal(B,0)
    harmonics=[(3,'cos')]+[(h,f)for h in range(5,H+1,2)for f in ('sin','cos')]
    basis=np.array([(np.sin if f=='sin'else np.cos)(h*theta)for h,f in harmonics])
    base=np.sin(3*theta);D=len(basis)
    aa=np.broadcast_to(np.arange(n)[:,None],(n,n-1)).ravel();wrap=np.zeros((n,n-1),dtype=np.int8);wrap[:,-1]=1
    def score(c):
        u=A*c[None,:]-B*c[:,None];np.fill_diagonal(u,np.inf)
        rows=np.argsort(u,axis=1)[:,:-1]
        tri=np.stack((aa,rows.ravel(),np.roll(rows,-1,axis=1).ravel()),axis=1);tri.sort(axis=1)
        keys=tri[:,0]*n*n+tri[:,1]*n+tri[:,2]
        _,inv,ct=np.unique(keys,return_inverse=True,return_counts=True)
        parity=np.bincount(inv,weights=wrap.ravel()).astype(int)%2
        return int(np.count_nonzero((ct==3)&(parity==0)))
    best=score(base);bestpar=np.zeros(D);start=time.monotonic();proposals=0;restarts=0;history=[]
    def retain(par,value):
        c=base+par@basis;ls=np.column_stack((np.sin(theta),np.cos(theta),c))
        aff=line_score(ls)
        certify(ls,out/f'n{n:03d}.json',aff,dict(projective_float=value,method_detail='odd Fourier support function',
                 seed=seed,harmonics=harmonics,coefficients=par.tolist(),proposals=proposals))
        row=dict(n=n,projective=value,affine=aff,seconds=time.monotonic()-start,proposals=proposals)
        history.append(row);print(json.dumps(row),flush=True)
    retain(bestpar,best)
    while time.monotonic()-start<seconds:
        restarts+=1
        if restarts%4==0:par=rng.normal(0,1,D)*10**rng.uniform(-5,-.1)
        else:par=bestpar+rng.normal(0,1,D)*10**rng.uniform(-7,-.7)
        c=base+par@basis;val=score(c)
        steps=max(1200,D*300)
        for step in range(steps):
            trial=par.copy();i=int(rng.integers(D));amplitude=10**rng.uniform(-7,0)
            trial[i]+=rng.normal()*amplitude;tc=base+trial@basis
            value=score(tc);proposals+=1
            temp=max(.04,.8*(1-step/steps))
            if value>=val or rng.random()<math.exp((value-val)/temp):par,c,val=trial,tc,value
            if val>best:
                try:retain(par,val)
                except RuntimeError:continue
                best=val;bestpar=par.copy()
            if proposals%200==0 and time.monotonic()-start>=seconds:break
    report=dict(n=n,seed=seed,H=H,best_projective_float=best,proposals=proposals,restarts=restarts,
                seconds=time.monotonic()-start,history=history,limitations='bounded heuristic; exact affine coordinate checks, projective verification separate')
    (out/f'n{n:03d}-report.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report),flush=True)

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--n',type=int,required=True);p.add_argument('--seconds',type=float,default=1800)
    p.add_argument('--seed',type=int,default=1331);p.add_argument('--harmonics',type=int,default=15);p.add_argument('--out',type=Path,required=True)
    a=p.parse_args();run(a.n,a.seconds,a.seed,a.out,a.harmonics)
