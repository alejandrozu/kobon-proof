"""Exact sparse rational-box exterior visibility for the refitted61 seed."""
from pathlib import Path
from fractions import Fraction as F
from functools import lru_cache
from itertools import combinations
import json
ROOT=Path(__file__).resolve().parents[3]
p=ROOT/'research/openmath-seven-hour-2026-10-05/constructions/contestant61-refitted-uniform-box.json'
raw=json.loads(p.read_text());ms=list(map(F,raw['slopes']));labels=raw['labels'];lo=list(map(F,raw['lo']));hi=list(map(F,raw['hi']));n=61
@lru_cache(None)
def orient(r,i,j):
    # Evaluate only the at-most-three supported parameter coordinates.
    f={}
    for k,c in [(i,ms[j]-ms[r]),(j,ms[r]-ms[i]),(r,ms[i]-ms[j])]:
        if labels[k]:
            pos,sgn=labels[k];f[pos]=f.get(pos,F(0))+c*ms[k]*sgn
    D=ms[j]-ms[i]
    return tuple((pos,c*D) for pos,c in sorted(f.items()) if c)
@lru_cache(None)
def low(f):return sum(c*(lo[pos] if c>=0 else hi[pos]) for pos,c in f)
@lru_cache(None)
def high(f):return sum(c*(hi[pos] if c>=0 else lo[pos]) for pos,c in f)
reports=[];best=[]
critical=sorted(set(-1/m for m in ms[1:]))
candidates=[critical[0]-1]+[(a+b)/2 for a,b in zip(critical,critical[1:])]+[critical[-1]+1]
for b in candidates:
    deriv=[[ (ms[i]-ms[r])*(-1-b*ms[i]) for i in range(n)] for r in range(n)]
    admissible=all(-1-b*m for m in ms)
    vis=[]
    if admissible:
        for i,j in combinations(range(n),2):
            okay=True
            for r in range(n):
                f=orient(r,i,j);di=deriv[r][i];dj=deriv[r][j]
                if not ((low(f)>=0 and di>=0 and dj>=0) or (high(f)<=0 and di<=0 and dj<=0)):
                    okay=False;break
            if okay:vis.append([i,j,n])
    rec=dict(normal=[str(F(1)),str(b)],admissible=admissible,visible_pairs=len(vis),right_pair=[0,60,61] in vis,right_direction=1+b*ms[-1]>0)
    reports.append(rec);print(rec,flush=True)
    if len(vis)>len(best) and rec['right_pair'] and rec['right_direction']:
        best=vis;win=rec
if best:
    raw.update(visible=best,normal=win['normal'],right_slope=str(ms[-1]),visibility_reports=reports)
    p.write_text(json.dumps(raw,indent=2)+'\n')
(ROOT/'research/openmath-seven-hour-2026-10-05/constructions/contestant61-visibility.json').write_text(json.dumps(dict(reports=reports,best=len(best),visible=best),indent=2)+'\n')