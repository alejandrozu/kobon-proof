"""Independent exact audit of boundary averaging and defect charging.
No floating angular calculations: one old line is the projective direction
chart pole, the other critical values are exact rational determinants.
"""
from pathlib import Path
from fractions import Fraction as F
from collections import Counter
import random,json,sys,itertools as it
ROOT=Path(__file__).resolve().parents[3]
sys.path.insert(0,str(ROOT/'research/kobon-hybrid'))
from exact_geometry import arrangement,primitive,read_lines
OUT=ROOT/'research/openmath-seven-hour-2026-10-05/constructions/boundary-averaging'
OUT.mkdir(parents=True,exist_ok=True)
def audit(lines,tag):
    ar=arrangement(lines);ls=ar['lines'];n=len(ls);T=len(ar['triangles'])
    assert len(ar['points'])==n*(n-1)//2,('not_simple',tag)
    ends=[]
    for i,row in enumerate(ar['rows']):
        assert len(row)==n-1 and row[0]!=row[-1]
        ends.extend([(i,row[0]),(i,row[-1])])
    counts=Counter(p for i,p in ends)
    assert all(v in(1,2) for v in counts.values())
    A=sum(v==1 for v in counts.values());B=sum(v==2 for v in counts.values())
    assert A+2*B==2*n
    delta=n*(n-2)-3*T
    assert B>=n-delta,(tag,B,n,delta)
    a0,b0,_=ls[0];u=(-b0,a0);v=(a0,b0)
    def det(x,y):return x[0]*y[1]-x[1]*y[0]
    critical=sorted(-F(det(l,u),det(l,v)) for l in ls[1:])
    assert len(set(critical))==n-1
    samples=[critical[0]-1]+[(a+b)/2 for a,b in zip(critical,critical[1:])]+[critical[-1]+1]
    normals=[(u[0]+s*v[0],u[1]+s*v[1]) for s in samples]
    normals += [(-a,-b) for a,b in normals]
    assert len(normals)==2*n
    faces={p:[i for i,q in ends if p==q] for p,count in counts.items() if count==2}
    occ=Counter();vs=[]
    for w in normals:
        assert all(det(l,w) for l in ls)
        chosen=[]
        for i,row in enumerate(ar['rows']):
            proj=lambda p:F(w[0]*p[0]+w[1]*p[1],p[2])
            p=max(row,key=proj)
            assert p in(row[0],row[-1])
            chosen.append((i,p))
        selected=Counter(p for i,p in chosen)
        vis=[p for p,count in selected.items() if count==2]
        occ.update(vis);vs.append(len(vis))
        # Independent direct sign/derivative test at each proposed visible pair.
        for p in vis:
            i,j=faces[p];x,y,z=p
            for r,l in enumerate(ls):
                val=l[0]*x+l[1]*y-l[2]*z
                dri=F(det(l,ls[i]),det(w,ls[i]));drj=F(det(l,ls[j]),det(w,ls[j]))
                assert (val>=0 and dri>=0 and drj>=0) or (val<=0 and dri<=0 and drj<=0)
    assert all(occ[p]==n-1 for p in faces),(tag,n,B,dict(occ))
    assert sum(vs)==(n-1)*B
    target=((n-1)*(n-delta)+2*n-1)//(2*n) if n>=delta else 0
    assert max(vs)>=target
    return dict(tag=tag,n=n,T=T,delta=delta,A=A,B=B,normal_sectors=len(normals),visible_sum=sum(vs),maximum_visible=max(vs),guaranteed_by_defect=target,all_double_extreme_occurrences=n-1,passed=True)
records=[]
for n in [11,33,49]:
    p=ROOT/f'research/finite-table/classical-{n:03d}.json'
    if p.exists():
        r=audit(read_lines(p),str(p.relative_to(ROOT)));records.append(r);print(r,flush=True)
raw=json.loads((ROOT/'research/openmath-seven-hour-2026-10-05/constructions/contestant61-refitted-uniform-box.json').read_text())
ms=list(map(F,raw['slopes']));labels=raw['labels'];lo=list(map(F,raw['lo']));hi=list(map(F,raw['hi']))
pars=[(l+h)/2 for l,h in zip(lo,hi)];pars[-1]=F(raw['epsilon_max'])
lines=[(0,1,0)]+[primitive((ms[i],-1,ms[i]*sgn*pars[pos])) for i,(pos,sgn) in enumerate(labels[1:],1)]
r=audit(lines,'refitted61 box midpoint');records.append(r);print(r,flush=True)
rng=random.Random(20261006)
for n in [3,4,5,6,7,8,9,10,12,15,18,21,24,30]:
    for sample in range(8):
        for attempt in range(100):
            ls=[(1,-s,rng.randrange(-1000000,1000001)) for s in rng.sample(range(-3000,3001),n)]
            ar=arrangement(ls)
            if len(ar['points'])==n*(n-1)//2:break
        r=audit(ls,f'random n{n} sample{sample}');records.append(r)
    print(dict(random_order=n,cases=8,passed=True),flush=True)
(OUT/'exact-audit.json').write_text(json.dumps(dict(scope='Exact finite validation; general theorem remains a separate Lean proof',random_seed=20261006,cases=records,total=len(records)),indent=2)+'\n')
print(dict(total=len(records),all_passed=True),flush=True)