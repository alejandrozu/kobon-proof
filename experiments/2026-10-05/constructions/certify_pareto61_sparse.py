"""Exact sparse true-tangent box and visibility validator for the Pareto61 proposal."""
from pathlib import Path
from fractions import Fraction as F
from collections import Counter
from functools import lru_cache
from itertools import combinations
import sys,json,time
R=Path(__file__).resolve().parents[3];sys.path.insert(0,str(R/'research/kobon-hybrid'))
from exact_geometry import arrangement,primitive
raw=json.loads((R/'research/openmath-seven-hour-2026-10-05/constructions/contestant61-refitted-uniform-box.json').read_text());proposal=json.loads((R/'research/openmath-seven-hour-2026-10-05/constructions/capcone-pareto-ray-seed61021/proposal-T1190-V29-ray000001.json').read_text())
u=[F(round((4-F(v))*10**10),10**10) for v in reversed(proposal['reciprocal_slopes'])];ms=[F(0)]+[1/v for v in u];labels=raw['labels'];n=61
base_lo=list(map(F,raw['lo']));base_hi=list(map(F,raw['hi']));start=time.time()
@lru_cache(None)
def ev(r,i,j):
 f={}
 for k,c in[(i,ms[j]-ms[r]),(j,ms[r]-ms[i]),(r,ms[i]-ms[j])]:
  if labels[k]:
   pos,sgn=labels[k];f[pos]=f.get(pos,F(0))+c*ms[k]*sgn
 return tuple((pos,c) for pos,c in sorted(f.items()) if c)
@lru_cache(None)
def orient(r,i,j):return tuple((pos,(ms[j]-ms[i])*c) for pos,c in ev(r,i,j))
for eta in[F(1,10**8),F(1,10**9),F(1,10**10),F(1,10**11)]:
 lo=base_lo.copy();hi=base_hi.copy();hi[-1]=eta;pars=[(l+h)/2 for l,h in zip(lo,hi)];pars[-1]=eta
 lines=[(0,1,0)]+[primitive((ms[i],-1,ms[i]*sgn*pars[k])) for i,(k,sgn) in enumerate(labels[1:],1)];ar=arrangement(lines);tris=sorted(ar['triangles']);caps=[t for t in tris if 0 in t]
 @lru_cache(None)
 def low(f):return sum(c*(lo[k] if c>=0 else hi[k]) for k,c in f)
 @lru_cache(None)
 def high(f):return sum(c*(hi[k] if c>=0 else lo[k]) for k,c in f)
 errors=[];simplechecks=trichecks=0
 for i,j,k in combinations(range(n),3):
  f=ev(k,i,j);simplechecks+=1
  if not(low(f)>0 or high(f)<0 or (f and all(pos==29 for pos,c in f))):errors.append(['simple',i,j,k]);break
 if not errors:
  for i,j,k in tris:
   for r in range(n):
    fs=[orient(r,a,b) for a,b in[(i,j),(i,k),(j,k)]];trichecks+=1
    if not(all(low(f)>=0 for f in fs) or all(high(f)<=0 for f in fs)):errors.append(['triangle',i,j,k,r]);break
   if errors:break
 rec=dict(T=len(tris),caps=len(caps),eta=str(eta),simple_checks=simplechecks,triangle_checks=trichecks,errors=errors,elapsed=time.time()-start);print(json.dumps(rec),flush=True)
 if errors or len(tris)!=1190 or len(caps)!=59:continue
 # Find the exact best positive-x normal at this rational point, using endpoint flags.
 flags={}
 for i,row in enumerate(ar['rows']):
  flags.setdefault(row[0],[]).append((i,-1));flags.setdefault(row[-1],[]).append((i,1))
 double={p:fs for p,fs in flags.items() if len(fs)==2};critical=sorted(-v for v in u);samples=[critical[0]-1]+[(x+y)/2 for x,y in zip(critical,critical[1:])]+[critical[-1]+1];wins=[]
 for b in samples:
  choice=[1]+[1 if 1+b*m>0 else-1 for m in ms[1:]]
  visible=[tuple(sorted((fs[0][0],fs[1][0])))+(n,) for fs in double.values() if all(choice[i]==sgn for i,sgn in fs)]
  if (0,60,61) in visible and 1+b*ms[-1]>0:wins.append((len(visible),b,sorted(visible)))
 for V,b,visible in sorted(wins,reverse=True):
  derivative=[[ (ms[i]-ms[r])*(-1-b*ms[i]) for i in range(n)] for r in range(n)];fails=[]
  for i,j,_ in visible:
   for r in range(n):
    f=orient(r,i,j);di=derivative[r][i];dj=derivative[r][j]
    if not((low(f)>=0 and di>=0 and dj>=0) or (high(f)<=0 and di<=0 and dj<=0)):fails.append([i,j,r]);break
   if fails:break
  print(json.dumps(dict(V=V,normal=['1',str(b)],errors=fails,elapsed=time.time()-start)),flush=True)
  if not fails and V>=29:
   out=dict(n=61,source_commit=raw['source_commit'],source='Rohith Poola point61:1190 credit; independent nonlocal cap-cone chamber mutation plus reflection and shear improves uniform visible resource',original_point_count=1190,triangles=tris,distinguished_triangles=caps,visible=visible,normal=['1',str(b)],slopes=[str(m) for m in ms],labels=labels,lo=[str(x) for x in lo],hi=[str(x) for x in hi],epsilon_max=str(eta),vertices=len(ar['points']),simple_checks=simplechecks,triangle_checks=trichecks,failures=[],tangent_enclosure_status='Actual BBLTangent60Bounds compiled; this new geometry still requires fresh Lean replay',right_slope=str(ms[-1]),exact_visibility=True,central_height_coefficient=str(2/(u[29]-u[30])))
   (R/'research/openmath-seven-hour-2026-10-05/constructions/contestant61-pareto-sparse-uniform-box.json').write_text(json.dumps(out,indent=2)+'\n');print('EXACT PARETO UNIFORM BOX PASS',flush=True);sys.exit(0)
raise RuntimeError('No whole box certified')
