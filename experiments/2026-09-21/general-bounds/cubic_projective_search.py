"""Nonuniform cubic-angle search scored in the projective plane.

Floating scores propose rational simple arrangements. Saved affine counts are
exact; projective counts require the independent exact chart census.
"""
import argparse,json,math,time
from pathlib import Path
import numpy as np
from cubic_search import certify,triangles

def score(theta):
    n=len(theta);u=np.cos(theta[:,None]+2*theta[None,:]);np.fill_diagonal(u,np.inf)
    rows=np.argsort(u,axis=1)[:,:-1]
    a=np.broadcast_to(np.arange(n)[:,None],(n,n-1)).ravel()
    tri=np.stack((a,rows.ravel(),np.roll(rows,-1,axis=1).ravel()),axis=1);tri.sort(axis=1)
    keys=tri[:,0]*n*n+tri[:,1]*n+tri[:,2]
    _,inv,count=np.unique(keys,return_inverse=True,return_counts=True)
    wrap=np.zeros((n,n-1),dtype=np.int8);wrap[:,-1]=1
    parity=np.bincount(inv,weights=wrap.ravel()).astype(int)%2
    return int(np.count_nonzero((count==3)&(parity==0)))

def run(n,seconds,seed,out,local=True):
    out.mkdir(parents=True,exist_ok=True);rng=np.random.default_rng(seed)
    grid=np.arange(n)*math.pi/n;theta=grid+.5*math.pi/n
    best=score(theta);start=time.monotonic();proposals=accepted=restarts=0;history=[]
    path=out/f'n{n:03d}.json';certify(theta,path,triangles(theta),dict(projective_float=best,seed=seed))
    print(json.dumps(dict(event='start',n=n,projective=best)),flush=True)
    while time.monotonic()-start<seconds:
        restarts+=1;scale=.001 if local else .45
        theta=grid+rng.uniform(-scale,scale,n)*math.pi/n;value=score(theta)
        for step in range(max(1000,100*n)):
            trial=theta.copy();i=int(rng.integers(n))
            trial[i]=grid[i]+rng.uniform(-scale,scale)*math.pi/n
            v=score(trial);proposals+=1
            temp=max(.05,1.2*(1-step/max(1000,100*n)))
            if v>=value or rng.random()<math.exp((v-value)/temp):
                theta,value=trial,v;accepted+=1
            if value>best:
                best=value;affine=triangles(theta)
                certify(theta,path,affine,dict(projective_float=best,seed=seed,proposals=proposals))
                row=dict(event='improvement',n=n,projective=best,affine=affine,seconds=time.monotonic()-start,proposals=proposals)
                history.append(row);print(json.dumps(row),flush=True)
            if proposals%200==0 and time.monotonic()-start>=seconds:break
    row=dict(n=n,local=local,seed=seed,projective_float=best,proposals=proposals,accepted=accepted,restarts=restarts,history=history,seconds=time.monotonic()-start)
    (out/f'n{n:03d}-report.json').write_text(json.dumps(row,indent=2)+'\n');print(json.dumps(row),flush=True)

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--n',type=int,required=True);p.add_argument('--seconds',type=float,default=600)
    p.add_argument('--seed',type=int,default=312);p.add_argument('--global-search',action='store_true');p.add_argument('--out',type=Path,required=True)
    a=p.parse_args();run(a.n,a.seconds,a.seed,a.out,not a.global_search)
