"""Search coordinated line-offset deformations by sweeping triple events.

For fixed normals and c(t)=c0+t*d, every change of order occurs when three
lines concur. Between such events the supporting triples stay unchanged.
The sweep visits all numerically separated events on a proposed direction;
it is a floating proposal engine, not an exact optimality certificate.
Every improvement is rationalized and independently checked before saving.
"""
from __future__ import annotations
import argparse,json,math,sys,time
from pathlib import Path
from itertools import combinations
from collections import Counter
from fractions import Fraction as F
import numpy as np

ROOT=Path(__file__).resolve().parents[3]
sys.path.insert(0,str(ROOT/'research/kobon-hybrid'))
from exact_geometry import arrangement,primitive
from verify_direct import verify

def normalized(lines):
    a=np.array([[float(F(v)) for v in row] for row in lines],dtype=float)
    a/=np.linalg.norm(a[:,:2],axis=1)[:,None]
    return a

class Sweep:
    def __init__(self,normals):
        self.normals=normals
        self.n=n=len(normals)
        self.det=normals[:,0,None]*normals[None,:,1]-normals[:,1,None]*normals[None,:,0]
        np.fill_diagonal(self.det,1)
        self.dot=normals@normals.T
        self.triples=np.array(list(combinations(range(n),3)),dtype=int)
        self.i,self.j,self.k=self.triples.T
        self.dij=self.det[self.i,self.j]
        self.dik=self.det[self.i,self.k]
        self.djk=self.det[self.j,self.k]
        self.numerical_fallbacks=0

    def intersection_parameters(self,c):
        u=(c[None,:]-c[:,None]*self.dot)/self.det
        np.fill_diagonal(u,np.inf)
        return u

    def determinant_values(self,c):
        return self.dij*c[self.k]-self.dik*c[self.j]+self.djk*c[self.i]

    def rows(self,c):
        return np.argsort(self.intersection_parameters(c),axis=1)[:,:-1]

    def score(self,c):
        rows=self.rows(c);n=self.n
        aa=np.broadcast_to(np.arange(n)[:,None],(n,n-2)).ravel()
        tris=np.stack((aa,rows[:,:-1].ravel(),rows[:,1:].ravel()),axis=1)
        tris.sort(axis=1)
        keys=tris[:,0]*n*n+tris[:,1]*n+tris[:,2]
        _,counts=np.unique(keys,return_counts=True)
        return int(np.count_nonzero(counts==3))

    def ray(self,c0,d,validate=False):
        n=self.n
        v0=self.determinant_values(c0);v1=self.determinant_values(d)
        if np.any(np.abs(v1)<1e-14):
            raise ArithmeticError('direction has a nearly persistent triple')
        events=-v0/v1
        order=np.argsort(events)
        rows=np.argsort(-self.intersection_parameters(d),axis=1)
        # Diagonal needs +infinity even after negation.
        slope=-self.intersection_parameters(d)
        np.fill_diagonal(slope,np.inf)
        rows=np.argsort(slope,axis=1)[:,:-1].tolist()
        positions=[[0]*n for _ in range(n)]
        frequencies=Counter()
        def key(a,b,c):
            a,b,c=sorted((a,b,c));return (a*n+b)*n+c
        for i,row in enumerate(rows):
            for j,x in enumerate(row):positions[i][x]=j
            for a,b in zip(row,row[1:]):frequencies[key(i,a,b)]+=1
        current=sum(v==3 for v in frequencies.values())
        best=current
        best_t=float(events[order[0]]-max(1,abs(events[order[0]])))
        checked=0
        def update(key,delta):
            nonlocal current
            old=frequencies[key]
            current-=old==3
            new=old+delta
            frequencies[key]=new
            current+=new==3
        def swap(i,a,b):
            pa,pb=positions[i][a],positions[i][b]
            if abs(pa-pb)!=1:return False
            lo=min(pa,pb);r=rows[i]
            affected=range(max(0,lo-1),min(n-2,lo+2))
            for j in affected:update(key(i,r[j],r[j+1]),-1)
            r[pa],r[pb]=r[pb],r[pa]
            positions[i][a],positions[i][b]=pb,pa
            for j in affected:update(key(i,r[j],r[j+1]),1)
            return True
        for ix,ev in enumerate(order):
            t=float(events[ev])
            nxt=float(events[order[ix+1]]) if ix+1<len(order) else t+2*max(1,abs(t))
            sample=(t+nxt)/2
            a,b,c=map(int,self.triples[ev])
            ok=swap(a,b,c) and swap(b,a,c) and swap(c,a,b)
            near=nxt-t<1e-10*max(1,abs(t),abs(nxt))
            if not ok or near:
                # Tied events are recomputed in the next open chamber. Rebuild
                # from geometry rather than asserting invalid adjacent swaps.
                self.numerical_fallbacks+=1
                rows=self.rows(c0+sample*d).tolist();frequencies.clear()
                for i,row in enumerate(rows):
                    for j,x in enumerate(row):positions[i][x]=j
                    for aa,bb in zip(row,row[1:]):frequencies[key(i,aa,bb)]+=1
                current=sum(v==3 for v in frequencies.values())
            if near:continue
            if validate and ix%max(1,len(order)//100)==0:
                brute=self.score(c0+sample*d)
                assert brute==current,(ix,brute,current)
                checked+=1
            if current>best:
                brute=self.score(c0+sample*d)
                if brute!=current:raise ArithmeticError(('sweep mismatch',brute,current))
                best=current;best_t=sample
        return best,best_t,checked

def certify(normals,c,expected,path,metadata):
    lines=np.column_stack((normals,c))
    for denominator in (10**6,10**9,10**12,10**15):
        ints=[]
        for row in lines:
            row=row/max(abs(row))
            ints.append(primitive([int(round(x*denominator)) for x in row]))
        ar=arrangement(ints)
        if len(ar['triangles'])!=expected or len(ar['points'])!=len(lines)*(len(lines)-1)//2:continue
        data=dict(n=len(lines),triangle_count=expected,lines_frac=[[str(v) for v in row] for row in ints],
                  construction='Coordinated line-offset deformation through a sweep of triple events',
                  proposal_arithmetic='floating point; accepted only after two independent exact counters',
                  **metadata)
        path.write_text(json.dumps(data,indent=2)+'\n',encoding='utf-8')
        result=verify(path)
        assert result['triangles']==expected
        return True
    return False

def main():
    p=argparse.ArgumentParser();p.add_argument('--input',type=Path,required=True)
    p.add_argument('--seconds',type=float,default=600);p.add_argument('--seed',type=int,default=1)
    p.add_argument('--out',type=Path,required=True);p.add_argument('--validate',action='store_true')
    args=p.parse_args();args.out.mkdir(parents=True,exist_ok=True)
    data=json.loads(args.input.read_text());lines=normalized(data['lines_frac'])
    normals=lines[:,:2];c0=lines[:,2].copy();n=len(lines);rng=np.random.default_rng(args.seed)
    sweep=Sweep(normals);initial=sweep.score(c0)
    assert initial==data['triangle_count'],(initial,data['triangle_count'])
    best=initial;best_c=c0.copy();working=c0.copy();theta=np.arctan2(normals[:,0],normals[:,1])
    start=time.monotonic();rays=0;chambers=0;failures=0;accepted=0;checks=0;history=[]
    while time.monotonic()-start<args.seconds:
        rays+=1
        mode=rays%4
        if mode==0:d=rng.normal(size=n)
        elif mode==1:
            h=int(rng.integers(2,max(3,n//2)))
            d=np.sin((2*h+1)*theta+rng.uniform(0,2*math.pi))+.000001*rng.normal(size=n)
        elif mode==2:
            d=sum(rng.normal()*np.sin(k*theta+rng.uniform(0,2*math.pi)) for k in (3,5,7,9))
            d+=.000001*rng.normal(size=n)
        else:
            d=rng.normal(size=n);mask=rng.random(n)<.25;d[~mask]*=.000001
        try:
            value,t,checked=sweep.ray(working,d,validate=args.validate and rays<=4)
        except ArithmeticError:
            failures+=1;continue
        chambers+=len(sweep.triples)+1;checks+=checked
        candidate=working+t*d
        if value>best:
            path=args.out/f'n{n:03d}-t{value:05d}-seed{args.seed}.json'
            if certify(normals,candidate,value,path,dict(random_seed=args.seed,ray=rays,source=str(args.input))):
                best=value;best_c=candidate.copy();working=candidate.copy();accepted+=1
                event=dict(seconds=time.monotonic()-start,ray=rays,triangles=best,file=path.name)
                history.append(event);print(json.dumps(event),flush=True)
        elif value>=best-2 and rng.random()<.35:
            working=candidate.copy()
        else:working=best_c.copy()
        if rays%50==0:print(json.dumps(dict(rays=rays,chambers=chambers,best=best,seconds=time.monotonic()-start)),flush=True)
    report=dict(n=n,seed=args.seed,input=str(args.input),initial=initial,best=best,
        seconds=time.monotonic()-start,rays=rays,chambers=chambers,arithmetic_failures=failures,
        tied_event_rebuilds=sweep.numerical_fallbacks,independent_sweep_checkpoints=checks,
        exact_improvements=accepted,history=history,
        limitations='A bounded numerical proposal search; no exhaustive optimality or novelty claim')
    (args.out/f'report-{n}-{args.seed}.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report),flush=True)

if __name__=='__main__':main()
