"""Topology screen of isolated four-line cluster collapses in the uniform61 seed.

Only actual contiguous clusters are considered. All distinguished cap apices
are excluded. A combinatorial score is not a straight-line realizability proof.
"""
from pathlib import Path
from fractions import Fraction as F
from collections import Counter
import json,sys,itertools as it,time,math
ROOT=Path(__file__).resolve().parents[3]
sys.path.insert(0,str(ROOT/'research/kobon-hybrid'))
sys.path.insert(0,str(Path(__file__).resolve().parent))
from exact_geometry import arrangement
from collapse_uniform61_triangles import collapsed_count

if __name__=='__main__':
    start=time.time();source=ROOT/'research/openmath-seven-hour-2026-10-05/constructions/contestant61-refitted-uniform-box.json';raw=json.loads(source.read_text());bounds=[(F(a)+F(b))/2 for a,b in zip(raw['lo'],raw['hi'])];roots=[bounds[p]*s for p,s in raw['labels'][1:]];h=[1/F(m) for m in raw['slopes'][1:]];lines=[(F(0),F(1),F(0))]+[(F(1),-hh,a) for hh,a in zip(h,roots)];ar=arrangement(lines);ids={p:i for i,p in enumerate(ar['points'])};pairs={tuple(sorted(s)):ids[p] for p,s in ar['points'].items()};pos=[{ids[p]:j for j,p in enumerate(row)} for row in ar['rows']];hist=Counter();records=[];tested=0
    for Q in it.combinations(range(1,61),4):
        if any(b==a+1 for a,b in zip(Q,Q[1:])):continue
        tested+=1
        valid=True
        for i in Q:
            xs=[pos[i][pairs[tuple(sorted((i,j)))]] for j in Q if j!=i]
            if max(xs)-min(xs)!=2:valid=False;break
        if not valid:continue
        T,caps=collapsed_count(ar,Q);hist[T]+=1;records.append(dict(Q=Q,T=T,caps=caps))
    out=ROOT/'research/openmath-seven-hour-2026-10-05/seed_search/collapse-uniform61';result=dict(quartets_tested=tested,contiguous_clusters=len(records),histogram=dict(hist),records=records,seconds=time.time()-start,scope='Isolated contiguous quartet topology only, no LP or geometric count claim')
    (out/'quartet-topology.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result),flush=True)
