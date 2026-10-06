"""Exact rational numerical BBL visibility audit; no universal theorem claim.
The tangent approximations below are diagnostics only, independently checked as
finite arrangements. The certified61 true-tangent family is unchanged.
"""
from pathlib import Path
from fractions import Fraction as F
from collections import Counter
import sys,json,time
R=Path(__file__).resolve().parents[3]
sys.path.insert(0,str(R/'research/kobon-hybrid'));sys.path.insert(0,str(R/'work/python-deps'))
from exact_geometry import primitive,arrangement
import mpmath as mp
mp.mp.dps=100
raw=json.loads((R/'research/openmath-seven-hour-2026-10-05/constructions/contestant61-refitted-uniform-box.json').read_text())
ms=list(map(F,raw['slopes']));labels=raw['labels'];lo=list(map(F,raw['lo']));hi=list(map(F,raw['hi']))
pars=[F(str(mp.tan(mp.pi*k/60))) for k in range(1,30)]+[F(raw['epsilon_max'])]
lines=[(0,1,0)]+[primitive((ms[i],-1,ms[i]*sgn*pars[pos])) for i,(pos,sgn) in enumerate(labels[1:],1)]
records=[]
for depth in range(3):
 start=time.time();ar=arrangement(lines);n=len(lines);assert len(ar['points'])==n*(n-1)//2
 counts=Counter(p for row in ar['rows'] for p in(row[0],row[-1]));faces={p for p,c in counts.items() if c==2}
 ends={p:[] for p in faces}
 for i,row in enumerate(ar['rows']):
  if row[0] in faces:ends[row[0]].append((i,-1))
  if row[-1] in faces:ends[row[-1]].append((i,1))
 pole=ar['lines'][0];a0,b0,_=pole;u=(-b0,a0);v=(a0,b0)
 def det(x,y):return x[0]*y[1]-x[1]*y[0]
 crit=sorted(-F(det(l,u),det(l,v)) for l in ar['lines'][1:]);samples=[crit[0]-1]+[(a+b)/2 for a,b in zip(crit,crit[1:])]+[crit[-1]+1]
 values=[];directions=[]
 for sg in(1,-1):
  for s in samples:
   w=(sg*(u[0]+s*v[0]),sg*(u[1]+s*v[1]));choices=[]
   for i,l in enumerate(ar['lines']):
    # row axis =x unless vertical, in which case y
    deriv=w[1] if not l[1] else w[0]-w[1]*F(l[0],l[1]);assert deriv
    choices.append(1 if deriv>0 else-1)
   values.append(sum(all(choices[i]==sgn for i,sgn in ends[p]) for p in faces));directions.append(w)
 assert sum(values)==(n-1)*len(faces)
 rec=dict(depth=depth,n=n,T=len(ar['triangles']),B=len(faces),max_visible=max(values),distribution=dict(Counter(values)),transported_visible=(n-1)//2-2,elapsed=time.time()-start)
 records.append(rec);print(rec,flush=True)
 if depth==2:break
 q=n-1;r=q//4;eta=F(1,10**(12+depth*32));kap=F(1,10**(30+depth*50))
 new=[]
 for i in range(q):
  beta=-mp.pi/2+(mp.mpf(i)+mp.mpf('0.5'))*mp.pi/q
  t=F(str(mp.tan(beta)));sf=2*t/(1+t*t)+eta/t;m=kap*sf
  new.append(primitive((m,-1,m*t)))
 # current lines are reindexed axis first, nonaxis sorted intercepts.
 arrangement_order=lines[1:]+new+[lines[0]]
 def perm(j):return q+j//2 if j<q and j%2==0 else j//2 if j<q else j//2 if j%2==0 else q+j//2
 lines=[arrangement_order[-1]]+[arrangement_order[perm(j)] for j in range(2*q)]
(R/'research/openmath-seven-hour-2026-10-05/constructions/bbl61-visibility-transport-audit.json').write_text(json.dumps(dict(scope='Exact rational finite diagnostics with high precision tangent approximations; not a uniform certificate',records=records),indent=2)+'\n')
