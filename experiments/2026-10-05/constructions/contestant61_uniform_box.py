"""Exact rational-box feasibility of a contestant-derived uniform 61 seed.
Numerical tangent values propose rational intervals. Finite box validation is exact;
those tangent enclosures themselves still require a Lean/analytic proof.
Source: Rohith Poola, rsi-kobon-triangles, pinned f462d8e18aea2a458376c523c9b6c2980237071f.
"""
from pathlib import Path
from fractions import Fraction as F
from functools import lru_cache
from itertools import combinations
import sys,json,time
ROOT=Path(__file__).resolve().parents[3]
sys.path.insert(0,str(ROOT/'work/python-deps'))
sys.path.insert(0,str(ROOT/'research/kobon-hybrid'))
import mpmath as mp
from exact_geometry import primitive,arrangement
mp.mp.dps=90
raw=json.loads((ROOT/'work/openmath-rohith/kobon-triangles/bases/n61_1190_base31.json').read_text())
ls=raw['lines'];n=len(ls);d=30
bounds=json.loads((ROOT/'research/openmath-seven-hour-2026-10-05/corpus/tangent60/bounds.json').read_text())
los=[F(bounds[str(k)][0]) for k in range(1,30)]
his=[F(bounds[str(k)][1]) for k in range(1,30)]
vals=[(l+h)/2 for l,h in zip(los,his)]
slopes=[F(0)];labels=[None]
for aa,bb,cc in ls[1:]:
    m=F(-aa,bb);x=F(-cc,aa)
    if abs(abs(x)-F(1,100))<F(1,10**18):j=29
    else:
        j=min(range(29),key=lambda k:abs(float(abs(x))-float(vals[k])))
        assert abs(float(abs(x))-float(vals[j]))<1e-10,(x,j)
    slopes.append(-m);labels.append([j,1 if x>0 else -1])
forms=[(F(0),)*d]+[tuple(slopes[i]*lab[1] if k==lab[0] else F(0) for k in range(d)) for i,lab in enumerate(labels[1:],1)]
# Test successively shrinking whole intervals, not only a saved epsilon.
for emax in [F(1,1000)]:
    lo=los+[F(0)];hi=his+[emax];mid=[(l+h)/2 for l,h in zip(lo,hi)];mid[-1]=emax
    concrete=[primitive([slopes[i],-1,sum(c*x for c,x in zip(forms[i],mid))]) for i in range(n)]
    ar=arrangement(concrete);tris=sorted(ar['triangles']);dist=[t for t in tris if 0 in t]
    @lru_cache(None)
    def det(i,j):return slopes[j]-slopes[i]
    @lru_cache(None)
    def ev(r,i,j):
        a,b,c=slopes[i],slopes[j],slopes[r]
        return tuple(c*(-forms[i][k]+forms[j][k])-(a*forms[j][k]-b*forms[i][k])-det(i,j)*forms[r][k] for k in range(d))
    @lru_cache(None)
    def lower(f):return sum(c*(lo[k] if c>=0 else hi[k]) for k,c in enumerate(f))
    @lru_cache(None)
    def upper(f):return sum(c*(hi[k] if c>=0 else lo[k]) for k,c in enumerate(f))
    @lru_cache(None)
    def orient(r,i,j):return tuple(det(i,j)*c for c in ev(r,i,j))
    failures=[];simplechecks=0;trichecks=0
    for i,j,k in combinations(range(n),3):
        f=ev(k,i,j);simplechecks+=1
        if not(lower(f)>0 or upper(f)<0 or (all(f[t]==0 for t in range(d-1)) and f[-1])):
            failures.append(['simplicity',i,j,k]);break
    if not failures:
        for i,j,k in tris:
            for r in range(n):
                fs=[orient(r,a,b) for a,b in [(i,j),(i,k),(j,k)]];trichecks+=1
                if not(all(lower(f)>=0 for f in fs) or all(upper(f)<=0 for f in fs)):
                    failures.append(['triangle',i,j,k,r]);break
            if failures:break
    record=dict(n=n,triangles=len(tris),distinguished=len(dist),epsilon_max=str(emax),vertices=len(ar['points']),simple_checks=simplechecks,triangle_checks=trichecks,failures=failures)
    print(record,flush=True)
    if not failures and len(tris)>=1182 and len(dist)==59:
        out=dict(record,source_commit='f462d8e18aea2a458376c523c9b6c2980237071f',source='Rohith Poola rsi-kobon-triangles; reflected across y=0 and central intercepts shrunk', original_point_count=1190, tangent_enclosure_status='Exact rational endpoints exported by BBLTangent60Bounds; Lean proof compilation pending separately',slopes=[str(x) for x in slopes],labels=labels,lo=[str(x) for x in lo],hi=[str(x) for x in hi],triangles=tris,distinguished_triangles=dist)
        (ROOT/'research/openmath-seven-hour-2026-10-05/constructions/contestant61-uniform-box.json').write_text(json.dumps(out,indent=2)+'\n')
        break