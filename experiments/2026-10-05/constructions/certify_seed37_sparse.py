"""Exact whole-box check of a37/431 fixed-slope compatibility proposal.
The proposed tangent intervals are deliberately wide; actual angle lemmas
must be supplied and compiled separately before this is a Lean family.
"""
from pathlib import Path
from fractions import Fraction as F
from functools import lru_cache
from itertools import combinations
import sys,json,time
R=Path(__file__).resolve().parents[3];sys.path.insert(0,str(R/'research/kobon-hybrid'));sys.path.insert(0,str(R/'work/python-deps'))
from exact_geometry import arrangement,primitive
import mpmath as mp
mp.mp.dps=90;n=37;q=36;d=18;D=10**20
p=R/'research/openmath-seven-hour-2026-10-05/seed_search/contestant37-construction-axis-probe/n037-axis004-eps0-proposal.json';proposal=json.loads(p.read_text());u=[F(round(F(v)*10**10),10**10) for v in proposal['reciprocal_slopes']];ms=[F(0)]+[1/v for v in u]
vals=[F(str(mp.tan(mp.pi*k/q))) for k in range(1,d)];width=F(1,10**15);base_lo=[F(((v-width)*D).__floor__(),D) for v in vals];base_hi=[F(((v+width)*D).__ceil__(),D) for v in vals]
labels=[None]+[[abs(k)-1,1 if k>0 else-1] for k in range(-(d-1),0)]+[[d-1,-1],[d-1,1]]+[[k-1,1] for k in range(1,d)]
assert len(labels)==n;start=time.time()
@lru_cache(None)
def ev(r,i,j):
 f={}
 for k,c in[(i,ms[j]-ms[r]),(j,ms[r]-ms[i]),(r,ms[i]-ms[j])]:
  if labels[k]:
   pos,sgn=labels[k];f[pos]=f.get(pos,F(0))+c*ms[k]*sgn
 return tuple((pos,c) for pos,c in sorted(f.items()) if c)
@lru_cache(None)
def orient(r,i,j):return tuple((pos,(ms[j]-ms[i])*c) for pos,c in ev(r,i,j))
for eta in[F(1,10**8),F(1,10**9),F(1,10**10)]:
 lo=base_lo+[F(0)];hi=base_hi+[eta];pars=[(l+h)/2 for l,h in zip(lo,hi)];pars[-1]=eta
 lines=[(0,1,0)]+[primitive((ms[i],-1,ms[i]*sgn*pars[k])) for i,(k,sgn) in enumerate(labels[1:],1)];ar=arrangement(lines);tris=sorted(ar['triangles']);caps=[t for t in tris if 0 in t]
 @lru_cache(None)
 def low(f):return sum(c*(lo[k] if c>=0 else hi[k]) for k,c in f)
 @lru_cache(None)
 def high(f):return sum(c*(hi[k] if c>=0 else lo[k]) for k,c in f)
 errors=[];simplechecks=trichecks=0
 for i,j,k in combinations(range(n),3):
  f=ev(k,i,j);simplechecks+=1
  if not(low(f)>0 or high(f)<0 or (f and all(pos==d-1 for pos,c in f))):errors.append(['simple',i,j,k]);break
 if not errors:
  for i,j,k in tris:
   for r in range(n):
    fs=[orient(r,a,b) for a,b in[(i,j),(i,k),(j,k)]];trichecks+=1
    if not(all(low(f)>=0 for f in fs) or all(high(f)<=0 for f in fs)):errors.append(['triangle',i,j,k,r]);break
   if errors:break
 rec=dict(T=len(tris),caps=len(caps),eta=str(eta),simple_checks=simplechecks,triangle_checks=trichecks,errors=errors,elapsed=time.time()-start);print(json.dumps(rec),flush=True)
 if not errors and len(tris)==431 and len(caps)==35:
  out=dict(n=n,T=431,source_commit=proposal['source_commit'],source='Rohith Poola37:431 point type on the known Parpalak-Utkin/Blanc q18 numerical orbit; independent fixed-slope uniform grid refit',triangles=tris,distinguished_triangles=caps,slopes=[str(m) for m in ms],labels=labels,lo=[str(x) for x in lo],hi=[str(x) for x in hi],epsilon_max=str(eta),vertices=len(ar['points']),simple_checks=simplechecks,triangle_checks=trichecks,failures=[],tangent_enclosure_status='Wide proposed actualtan36 intervals; actual BBLTangent36Bounds proof pending',central_height_coefficient=str(2/(u[d-1]-u[d])))
  (R/'research/openmath-seven-hour-2026-10-05/constructions/contestant37-uniform-box.json').write_text(json.dumps(out,indent=2)+'\n');(R/'research/openmath-seven-hour-2026-10-05/constructions/tangent36-proposed-wide-bounds.json').write_text(json.dumps({str(k):[str(base_lo[k-1]),str(base_hi[k-1])] for k in range(1,d)},indent=2)+'\n');print('EXACT37 BOX PASS',flush=True);break
else:raise RuntimeError('No whole box certified')
