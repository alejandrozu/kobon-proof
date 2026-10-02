"""Independently implemented analytic-gradient pseudoline straightening.

Input words are attributed to Parpalak--Utkin (arXiv:2607.29236). The angle
and distance hinge strategy follows Savchuk (arXiv:2507.07951), with an analytic
gradient and seeded restarts. Neither a numerical minimum nor a failed run is
a stretchability proof. Every retained coordinate count is independently exact.
"""
from pathlib import Path
import os
os.environ.setdefault('OMP_NUM_THREADS','1');os.environ.setdefault('OPENBLAS_NUM_THREADS','1')
import sys,json,math,time,argparse,hashlib,itertools as it
ROOT=Path(__file__).resolve().parents[2]
sys.path.insert(0,str(ROOT/'work/construction-deps'))
sys.path.insert(0,str(ROOT/'research/kobon-hybrid'))
import numpy as np
from scipy.optimize import minimize,linprog
from exact_geometry import arrangement
from verify_direct import verify


def read_word(path,index):
    raw=[line for line in path.read_text().splitlines() if ')' in line][index]
    word=list(map(int,raw.split(')',1)[1].split()));n=max(word)+2
    assert len(word)==n*(n-1)//2
    perm=list(range(n));rows=[[] for _ in range(n)];seen=set()
    for g in word:
        i,j=perm[g:g+2];assert i<j and (i,j) not in seen
        seen.add((i,j));rows[i].append(j);rows[j].append(i);perm[g],perm[g+1]=j,i
    assert perm==list(range(n))[::-1]
    constraints=[]
    for i,row in enumerate(rows):
        for j,k in zip(row,row[1:]):constraints.append((i,j,k,-np.sign(j-i)*np.sign(k-i)))
    # Independent combinatorial triangle count: every side is consecutive.
    counts={}
    for i,row in enumerate(rows):
        for j,k in zip(row,row[1:]):
            t=tuple(sorted((i,j,k)));counts[t]=counts.get(t,0)+1
    triangles=sum(v==3 for v in counts.values())
    return n,np.array(constraints,dtype=int),triangles


class Objective:
    def __init__(self,n,constraints,eps=.001,min_gap=.00001,gap_weight=100):
        self.n=n;self.i,self.j,self.k,self.s=constraints.T;self.eps=eps;self.min_gap=min_gap;self.gap_weight=gap_weight
        self.weights=np.ones(len(self.i))

    def values(self,x):
        a=x[:self.n];c=x[self.n:];i,j,k=self.i,self.j,self.k
        u=a[k]-a[j];v=a[i]-a[k];w=a[j]-a[i]
        return (c[i]*np.sin(u)+c[j]*np.sin(v)+c[k]*np.sin(w))*self.s

    def __call__(self,x):
        n=self.n;a=x[:n];c=x[n:];i,j,k=self.i,self.j,self.k;s=self.s
        u=a[k]-a[j];v=a[i]-a[k];w=a[j]-a[i]
        su,sv,sw=np.sin(u),np.sin(v),np.sin(w)
        cu,cv,cw=np.cos(u),np.cos(v),np.cos(w)
        f=c[i]*su+c[j]*sv+c[k]*sw
        bad=np.maximum(self.eps-s*f,0);factor=-2*bad*s*self.weights
        grad_a=(np.bincount(i,weights=factor*(c[j]*cv-c[k]*cw),minlength=n)+
                np.bincount(j,weights=factor*(-c[i]*cu+c[k]*cw),minlength=n)+
                np.bincount(k,weights=factor*(c[i]*cu-c[j]*cv),minlength=n))
        grad_c=(np.bincount(i,weights=factor*su,minlength=n)+
                np.bincount(j,weights=factor*sv,minlength=n)+
                np.bincount(k,weights=factor*sw,minlength=n))
        gaps=np.r_[np.diff(a),math.pi-a[-1]+a[0]]
        bg=np.minimum(gaps-self.min_gap,0)+np.maximum(gaps-4*math.pi/(n-1),0)
        dg=2*self.gap_weight*bg
        grad_a+=np.roll(dg,1)-dg
        return float(np.dot(bad*bad,self.weights)+self.gap_weight*np.dot(bg,bg)),np.r_[grad_a,grad_c]


def lines_of(x,n,digits=12):
    a=x[:n];c=x[n:];scale=10**digits
    return [(int(round(math.cos(t)*scale)),int(round(math.sin(t)*scale)),int(round(z*scale))) for t,z in zip(a,c)]


def run(path,out,seconds,seed,index,balanced=False):
    path=path.resolve();out.mkdir(parents=True,exist_ok=True);n,cons,target=read_word(path,index);rng=np.random.default_rng(seed)
    obj=Objective(n,cons,min_gap=.1,gap_weight=.001) if balanced else Objective(n,cons)
    start=time.time();best=-1;events=[];attempt=0;pool=[]
    print(json.dumps(dict(event='start',n=n,pseudoline_target=target,constraints=len(cons),seed=seed)),flush=True)
    while time.time()-start<seconds:
        attempt+=1
        if pool and attempt%3:
            base=pool[rng.integers(len(pool))].copy()
            base[:n]+=rng.normal(0,.002 if attempt%2 else .02,n)
            base[n:]+=rng.normal(0,.01 if attempt%2 else .1,n)
            base[:n]=np.clip(np.sort(base[:n]),1e-5,math.pi-1e-5)
        else:
            a=(np.arange(n)+.5)*math.pi/n
            c=.1*(-1.)**np.arange(n)
            if attempt>1:c+=rng.normal(0,.2,n)
            base=np.r_[a,c]
        obj.eps=float(rng.choice([.001,.01,.03,.1])) if balanced else (float(rng.choice([.00001,.0001,.001,.01])) if attempt>1 else .001)
        obj.weights=np.ones(len(cons)) if attempt%4 else rng.lognormal(0,.7,len(cons))
        def callback(x):
            if time.time()-start>=seconds:raise StopIteration
        result=minimize(obj,base,method='L-BFGS-B',jac=True,bounds=[(1e-7,math.pi-1e-7)]*n+[(-100,100)]*n,
                        callback=callback,options={'maxiter':7000,'maxls':40,'ftol':1e-16,'gtol':1e-10,'maxcor':30})
        x=result.x;values=obj.values(x);violations=int(np.sum(values<=0));margin=float(values.min())
        lines=lines_of(x,n);rejection=None
        try:
            ar=arrangement(lines);count=len(ar['triangles']);simple=len(ar['points'])==n*(n-1)//2
        except AssertionError as exc:
            count=0;simple=False;rejection='Exact geometry rejected rounded proposal: '+str(exc)
        event=dict(attempt=attempt,triangles=count,simple=simple,target_violations=violations,
                   minimum_margin=margin,loss=float(result.fun),iterations=int(result.nit),
                   epsilon=obj.eps,seconds=time.time()-start,result=str(result.message))
        events.append(event)
        if rejection:event['coordinate_rejection']=rejection
        if simple and count>best:
            best=count;pool=[x.copy()]
            dest=out/f'n{n:03d}-best.json'
            dest.write_text(json.dumps(dict(n=n,triangle_count=count,simple=True,lines_frac=[[str(z) for z in l]for l in lines],
                source=str(path.relative_to(ROOT)),source_sha256=hashlib.sha256(path.read_bytes()).hexdigest(),
                input_attribution='Parpalak--Utkin pseudoline word, arXiv:2607.29236',
                method_attribution='Angle/distance hinge straightening inspired by Savchuk, arXiv:2507.07951',
                construction='Independent analytic-gradient straightening with seeded restarts',event=event),indent=2)+'\n')
            event['independent_verification']=verify(dest)
            print(json.dumps(dict(event='best',**event)),flush=True)
        elif simple and count>=best-2 and len(pool)<8:pool.append(x.copy())
        report=dict(source=str(path.relative_to(ROOT)),n=n,pseudoline_target=target,straight_line_best=best,
                    seed=seed,time_limit=seconds,attempts=attempt,elapsed=time.time()-start,events=events,balanced=balanced,
                    scope='Bounded nonlinear search. Failure is not a proof of nonstretchability; exact verification applies only to saved coordinate counts.')
        (out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
        if best==target:break
    print(json.dumps(dict(event='done',n=n,best=best,target=target,attempts=attempt,seconds=time.time()-start)),flush=True)


if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('input',type=Path);p.add_argument('--out',type=Path,required=True)
    p.add_argument('--seconds',type=float,default=300);p.add_argument('--seed',type=int,default=20261002);p.add_argument('--index',type=int,default=0)
    p.add_argument('--balanced',action='store_true')
    a=p.parse_args();run(a.input,a.out,a.seconds,a.seed,a.index,a.balanced)
