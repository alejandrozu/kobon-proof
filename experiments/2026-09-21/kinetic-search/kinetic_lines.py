"""Joint slope/intercept chamber sweeps, with exact acceptance of improvements.

Lines are a_i(t)x+y=c_i(t). Triple events have quadratic equations;
parallel events have linear equations and move a crossing through infinity.
The numerical sweep is a proposal engine, not an exhaustive proof.
"""
from __future__ import annotations
import argparse,json,math,time
from pathlib import Path
from itertools import combinations
from collections import Counter
import numpy as np
from kinetic_offsets import normalized,certify

class Sweep:
    def __init__(self,n):
        self.n=n
        self.triples=np.array(list(combinations(range(n),3)),dtype=int)
        self.pairs=np.array(list(combinations(range(n),2)),dtype=int)
        self.i,self.j,self.k=self.triples.T
        self.numerical_fallbacks=0

    def rows(self,a,c):
        den=a[:,None]-a[None,:]
        np.fill_diagonal(den,1)
        xs=(c[:,None]-c[None,:])/den
        np.fill_diagonal(xs,np.inf)
        return np.argsort(xs,axis=1)[:,:-1]

    def score(self,a,c):
        rows=self.rows(a,c);n=self.n
        aa=np.broadcast_to(np.arange(n)[:,None],(n,n-2)).ravel()
        tris=np.stack((aa,rows[:,:-1].ravel(),rows[:,1:].ravel()),axis=1)
        tris.sort(axis=1)
        keys=tris[:,0]*n*n+tris[:,1]*n+tris[:,2]
        _,counts=np.unique(keys,return_counts=True)
        return int(np.count_nonzero(counts==3))

    def events(self,a,c,da,dc):
        i,j,k=self.i,self.j,self.k
        aj,ak,cj,ck=a[j]-a[i],a[k]-a[i],c[j]-c[i],c[k]-c[i]
        dj,dk,ej,ek=da[j]-da[i],da[k]-da[i],dc[j]-dc[i],dc[k]-dc[i]
        aa=dj*ek-dk*ej
        bb=dj*ck+aj*ek-dk*cj-ak*ej
        cc=aj*ck-ak*cj
        disc=bb*bb-4*aa*cc
        ids=np.arange(len(i));ts=[];ev=[]
        quadratic=(np.abs(aa)>1e-14)&(disc>1e-18)
        ix=ids[quadratic]
        qr=-.5*(bb[ix]+np.where(bb[ix]>=0,1.,-1.)*np.sqrt(disc[ix]))
        ts.extend((qr/aa[ix],cc[ix]/qr));ev.extend((ix,ix))
        linear=(np.abs(aa)<=1e-14)&(np.abs(bb)>1e-14)
        ts.append(-cc[linear]/bb[linear]);ev.append(ids[linear])
        p,q=self.pairs.T
        dd=da[p]-da[q]
        mask=np.abs(dd)>1e-14
        ts.append(-(a[p[mask]]-a[q[mask]])/dd[mask])
        ev.append(-np.arange(1,len(p)+1)[mask])
        times=np.concatenate(ts);events=np.concatenate(ev)
        valid=np.isfinite(times)&(np.abs(times)<1e10)
        times=times[valid];events=events[valid]
        order=np.argsort(times)
        return times[order],events[order]

    def ray(self,a,c,da,dc,threshold,rng,validate=False):
        n=self.n;times,events=self.events(a,c,da,dc)
        t0=times[0]-max(1,abs(times[0]))
        rows=self.rows(a+t0*da,c+t0*dc).tolist()
        positions=[[0]*n for _ in range(n)];frequencies=Counter()
        current=0
        def key(i,j,k):
            i,j,k=sorted((i,j,k));return (i*n+j)*n+k
        def rebuild(sample):
            nonlocal rows,current
            rows=self.rows(a+sample*da,c+sample*dc).tolist();frequencies.clear()
            for i,row in enumerate(rows):
                for j,x in enumerate(row):positions[i][x]=j
                for x,y in zip(row,row[1:]):frequencies[key(i,x,y)]+=1
            current=sum(v==3 for v in frequencies.values())
        rebuild(t0)
        best=current;best_t=t0;checked=0;seen=0;walk_t=None;walk_score=None
        def update(k,delta):
            nonlocal current
            old=frequencies[k];current-=old==3
            new=old+delta;frequencies[k]=new;current+=new==3
        def swap(i,x,y):
            px,py=positions[i][x],positions[i][y]
            if abs(px-py)!=1:return False
            lo=min(px,py);r=rows[i]
            affected=range(max(0,lo-1),min(n-2,lo+2))
            for j in affected:update(key(i,r[j],r[j+1]),-1)
            r[px],r[py]=r[py],r[px]
            positions[i][x],positions[i][y]=py,px
            for j in affected:update(key(i,r[j],r[j+1]),1)
            return True
        def infinity(i,j):
            p=positions[i][j];r=rows[i]
            if p==0:
                update(key(i,r[0],r[1]),-1)
                r.append(r.pop(0))
                update(key(i,r[-2],r[-1]),1)
            elif p==n-2:
                update(key(i,r[-2],r[-1]),-1)
                r.insert(0,r.pop())
                update(key(i,r[0],r[1]),1)
            else:return False
            for p,x in enumerate(r):positions[i][x]=p
            return True
        for ix,(t,ev) in enumerate(zip(times,events)):
            nxt=times[ix+1] if ix+1<len(times) else t+2*max(1,abs(t))
            sample=(t+nxt)/2
            if ev>=0:
                i,j,k=map(int,self.triples[ev]);ok=swap(i,j,k) and swap(j,i,k) and swap(k,i,j)
            else:
                i,j=map(int,self.pairs[-ev-1]);ok=infinity(i,j) and infinity(j,i)
            near=nxt-t<1e-10*max(1,abs(t),abs(nxt))
            if not ok or near:
                self.numerical_fallbacks+=1;rebuild(sample)
            if near:continue
            if validate and ix%max(1,len(events)//100)==0:
                brute=self.score(a+sample*da,c+sample*dc)
                if brute!=current:raise ArithmeticError(('checkpoint mismatch',ix,brute,current))
                checked+=1
            if current>best:
                brute=self.score(a+sample*da,c+sample*dc)
                if brute!=current:raise ArithmeticError(('maximum mismatch',ix,brute,current))
                best=current;best_t=sample
            if current>=threshold:
                seen+=1
                if rng.random()<1/seen:walk_t=sample;walk_score=current
        return best,best_t,walk_t,walk_score,len(events)+1,checked

def precondition(a,c):
    a=a-a.mean();c=c-c.mean()
    a=a/max(1,np.std(a));c=c/max(1e-8,np.std(c))
    return a,c

def main():
    p=argparse.ArgumentParser();p.add_argument('--input',type=Path,required=True)
    p.add_argument('--seconds',type=float,default=900);p.add_argument('--seed',type=int,default=1)
    p.add_argument('--out',type=Path,required=True);p.add_argument('--validate',action='store_true')
    p.add_argument('--depth',type=int,default=4)
    args=p.parse_args();args.out.mkdir(parents=True,exist_ok=True)
    data=json.loads(args.input.read_text());lines=normalized(data['lines_frac']);n=len(lines)
    # Choose a global rotation with every b coefficient separated from zero.
    angles=np.linspace(0,math.pi,1001)[:-1]
    angle=max(angles,key=lambda t:min(abs(lines[:,0]*math.sin(t)+lines[:,1]*math.cos(t))))
    aa=lines[:,0]*math.cos(angle)-lines[:,1]*math.sin(angle)
    bb=lines[:,0]*math.sin(angle)+lines[:,1]*math.cos(angle)
    a,c=precondition(aa/bb,lines[:,2]/bb)
    sweep=Sweep(n);initial=sweep.score(a,c)
    assert initial==data['triangle_count'],(initial,data['triangle_count'])
    rng=np.random.default_rng(args.seed);best=initial;best_a=a.copy();best_c=c.copy()
    start=time.monotonic();rays=0;chambers=0;failures=0;checks=0;history=[];walks=0
    while time.monotonic()-start<args.seconds:
        rays+=1;mode=rays%4
        da=rng.normal(size=n);dc=rng.normal(size=n)
        if mode==0:da*=0
        elif mode==1:dc*=0
        elif mode==2:da*=10**rng.uniform(-2,2)
        else:
            mask=rng.random(n)<.25;da[~mask]*=1e-6;dc[~mask]*=1e-6
        try:
            value,t,wt,wv,visits,ck=sweep.ray(a,c,da,dc,best-args.depth,rng,
                validate=args.validate and rays<=10)
        except ArithmeticError as e:
            failures+=1
            if failures<=10:print(json.dumps(dict(failed_ray=rays,error=str(e))),flush=True)
            a,c=best_a.copy(),best_c.copy();continue
        chambers+=visits;checks+=ck
        if value>best:
            ca,cc=precondition(a+t*da,c+t*dc)
            normals=np.column_stack((ca,np.ones(n)))
            path=args.out/f'n{n:03d}-t{value:05d}-seed{args.seed}.json'
            if certify(normals,cc,value,path,dict(random_seed=args.seed,ray=rays,source=str(args.input),
                method_detail='joint slopes and intercepts; quadratic concurrency and linear infinity events')):
                best=value;best_a=ca.copy();best_c=cc.copy()
                event=dict(seconds=time.monotonic()-start,ray=rays,triangles=best,file=path.name)
                history.append(event);print(json.dumps(event),flush=True)
        if wt is not None and rng.random()<.9:
            a,c=precondition(a+wt*da,c+wt*dc);walks+=1
            if sweep.score(a,c)!=wv:
                failures+=1;a,c=best_a.copy(),best_c.copy()
        else:a,c=best_a.copy(),best_c.copy()
        if rays%25==0:print(json.dumps(dict(rays=rays,chambers=chambers,best=best,
            current=sweep.score(a,c),seconds=round(time.monotonic()-start,2))),flush=True)
    report=dict(n=n,seed=args.seed,input=str(args.input),initial=initial,best=best,
        seconds=time.monotonic()-start,rays=rays,chambers=chambers,arithmetic_failures=failures,
        tied_event_rebuilds=sweep.numerical_fallbacks,independent_sweep_checkpoints=checks,
        exact_improvements=len(history),history=history,plateau_or_annealing_walks=walks,
        limitations='Bounded numerical proposals; no exhaustive optimality or priority claim')
    (args.out/f'report-{n}-{args.seed}.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report),flush=True)

if __name__=='__main__':main()
