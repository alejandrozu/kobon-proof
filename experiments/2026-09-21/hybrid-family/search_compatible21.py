"""Constrained tangent-grid search for a perfect 21-line BBL seed.

Floating crossing orders propose candidates only. Every apparent improvement
is independently rechecked with exact rational arithmetic before promotion.
The 20 distinguished-line segments must support all 19 possible triangles.
"""
from pathlib import Path
from fractions import Fraction as F
from itertools import combinations
import json,math,random,sys,time
import numpy as np

ROOT=Path(__file__).resolve().parents[3]
sys.path.insert(0,str(ROOT/'research/kobon-hybrid'))
from exact_geometry import arrangement,primitive,read_lines
from verify_direct import verify

OUT=Path(__file__).parent/'compatible21-search'
OUT.mkdir(exist_ok=True)
seed=read_lines(ROOT/'research/kobon-hybrid/certificates/n021.json')
ordered=sorted(seed[1:],key=lambda z:F(z[2],z[0]))
aa=[F(z[2],z[0]) for z in ordered]
vv=[-F(z[1],z[0]) for z in ordered]
A=np.array(list(map(float,aa)))
V0=np.array(list(map(float,vv)))
N=21;Q=20
TR=np.array(list(combinations(range(N),3)),dtype=np.int64)
I,J,K=TR.T
PAIRS=np.array(list(combinations(range(Q),2)))
RNG=random.Random(20260922)


def count(v):
    with np.errstate(divide='ignore',invalid='ignore',over='ignore'):
        ys=(A[:,None]-A[None,:])/(v[:,None]-v[None,:])
    if np.any(~np.isfinite(ys[~np.eye(Q,dtype=bool)])):return -1000,0
    coords=np.empty((N,N));coords[0,0]=np.inf
    coords[0,1:]=A;coords[1:,0]=0.;coords[1:,1:]=ys
    np.fill_diagonal(coords,np.inf)
    ranks=np.argsort(np.argsort(coords,axis=1,kind='stable'),axis=1,kind='stable')
    good=(np.abs(ranks[I,J]-ranks[I,K])==1)&(np.abs(ranks[J,I]-ranks[J,K])==1)&(np.abs(ranks[K,I]-ranks[K,J])==1)
    return int(good.sum()),int(good[I==0].sum())


def critical(v,i):
    p=PAIRS[(PAIRS[:,0]!=i)&(PAIRS[:,1]!=i)]
    j,k=p.T
    x=v[j]+(A[i]-A[j])/(A[j]-A[k])*(v[j]-v[k])
    return np.unique(np.concatenate((x,v[np.arange(Q)!=i])))


def proposal(v,i,wide=False):
    xs=critical(v,i)
    pos=int(np.searchsorted(xs,v[i]))
    if wide:
        p=RNG.randrange(len(xs)+1)
    else:
        jump=RNG.choice([-3,-2,-1,0,1,2,3])
        p=max(0,min(len(xs),pos+jump))
    if p==0:z=xs[0]-max(1.,abs(xs[0]))*RNG.uniform(.01,1)
    elif p==len(xs):z=xs[-1]+max(1.,abs(xs[-1]))*RNG.uniform(.01,1)
    else:
        lo,hi=xs[p-1],xs[p]
        z=lo+(hi-lo)*RNG.uniform(.1,.9)
    w=v.copy();w[i]=z
    return w


def exact_check(v,tag):
    lines=[(0,1,0)]+[primitive((F(1),-F(str(float(x))),a)) for a,x in zip(aa,v)]
    ar=arrangement(lines)
    T=len(ar['triangles']);C=sum(0 in t for t in ar['triangles'])
    result=dict(triangles=T,caps=C,simple=len(ar['points'])==N*(N-1)//2,
                V=[str(F(str(float(x)))) for x in v])
    if T>=133 and C==19 and result['simple']:
        path=OUT/f'candidate-{tag}.json'
        data=dict(n=N,triangle_count=T,lines_frac=[[str(z) for z in l] for l in lines],
                  construction='Constrained tangent-grid reciprocal-slope search',
                  priority_status='Unestablished; floating proposal verified with exact rational counters')
        path.write_text(json.dumps(data,indent=2)+'\n')
        result['direct']=verify(path)
        result['path']=str(path.relative_to(ROOT))
    return result


def main(seconds=3600):
    start=time.monotonic();last=start;steps=accepted=0;checks=[]
    v=V0.copy();T,C=count(v);assert (T,C)==(132,19),(T,C)
    pool=[v.copy()];best=132;current=T
    print('START compatible21',T,C,flush=True)
    while time.monotonic()-start<seconds:
        steps+=1
        if steps%5000==0:
            v=RNG.choice(pool).copy();current=count(v)[0]
        temp=RNG.choice([.05,.15,.3,.6,1.2]) if steps%5000==1 else temp if steps>1 else .3
        w=proposal(v,RNG.randrange(Q),wide=RNG.random()<.12)
        t,c=count(w)
        if c!=19:continue
        if t>=133:
            result=exact_check(w,steps);checks.append(dict(step=steps,floating=t,**result))
            (OUT/'candidate-checks.json').write_text(json.dumps(checks,indent=2)+'\n')
            print('EXACT CHECK',checks[-1],flush=True)
            if result['triangles']>=133 and result['caps']==19 and result['simple']:
                print('SUCCESS',flush=True);break
        if t>=current or RNG.random()<math.exp(max(-100.,(t-current)/temp)):
            v=w;current=t;accepted+=1
            if t==best and RNG.random()<.04:
                if len(pool)<250:pool.append(v.copy())
                else:pool[RNG.randrange(len(pool))]=v.copy()
        now=time.monotonic()
        if now-last>=30:
            report=dict(steps=steps,accepted=accepted,current=current,best=best,pool=len(pool),
                        seconds=round(now-start,3),exact_checks=len(checks),
                        scope='Floating search only; exact checks recorded separately')
            (OUT/'progress.json').write_text(json.dumps(report,indent=2)+'\n')
            np.save(OUT/'pool.npy',np.stack(pool))
            print(json.dumps(report),flush=True);last=now
    report=dict(steps=steps,accepted=accepted,seconds=round(time.monotonic()-start,3),
                best=best,pool=len(pool),exact_checks=checks,completed=True)
    (OUT/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    np.save(OUT/'pool.npy',np.stack(pool))
    print(json.dumps(report),flush=True)

if __name__=='__main__':main(float(sys.argv[1]) if len(sys.argv)>1 else 3600)
