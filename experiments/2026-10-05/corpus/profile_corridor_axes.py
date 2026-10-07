"""Exact corridor-axis combinatorics for the published even witnesses.

All vertex ranks, triangle-side apices and line membership are exact rational
data. A proposed singular tangent-grid model is a separate feasibility target.
"""
from pathlib import Path
from fractions import Fraction as F
from collections import Counter
import itertools as it,json,sys
ROOT=Path(__file__).resolve().parents[3];sys.path.insert(0,str(ROOT/'research/kobon-hybrid'))
from exact_geometry import arrangement

if __name__=='__main__':
    sources=[(n,ROOT/f'research/six-hour-2026-09-21/general-bounds/parpalak-utkin-current/certificate-{n:03d}.json') for n in [8,14,20,26,32,38,50]]+[(50,ROOT/'work/openmath-rohith/kobon-triangles/submissions/n50/solution.json')];records=[]
    for n,source in sources:
        raw=json.loads(source.read_text());ll=[tuple(map(F,l)) for l in raw['lines_frac']] if 'lines_frac' in raw else [(F(a),F(b),-F(c)) for a,b,c in raw['lines']];ar=arrangement(ll);cores=[p for p,s in ar['points'].items() if len(s)>=3];common=set.intersection(*(set(ar['points'][p]) for p in cores));axis=next(iter(common));row=ar['rows'][axis];pairpoints={tuple(sorted(p)):q for q,s in ar['points'].items() for p in it.combinations(s,2)};axis_tri=[]
        for labels,vertices in zip(ar['triangles'],ar['triangle_vertices']):
            if axis not in labels:continue
            base=[p for p in vertices if axis in ar['points'][p]];apex=next(p for p in vertices if p not in base);ranks=sorted(row.index(p) for p in base);assert ranks[1]==ranks[0]+1
            a,b,c=ll[axis];value=a*F(apex[0],apex[2])+b*F(apex[1],apex[2])-c;axis_tri.append(dict(labels=labels,ranks=ranks,side=1 if value>0 else -1,apex=list(map(str,apex))))
        intervals=[[] for _ in range(len(row)-1)]
        for t in axis_tri:intervals[t['ranks'][0]].append(t['side'])
        r=dict(n=n,T=len(ar['triangles']),source=str(source.relative_to(ROOT)),axis=axis,distinct_axis_vertices=len(row),core_ranks=[dict(rank=row.index(p),lines=sorted(ar['points'][p]),point=list(map(str,p))) for p in cores],interval_triangle_sides=intervals,axis_triangle_count=len(axis_tri),axis_triangles=axis_tri)
        records.append(r);print(json.dumps({k:r[k] for k in ['n','axis','distinct_axis_vertices','core_ranks','axis_triangle_count','interval_triangle_sides']}),flush=True)
    out=ROOT/'research/openmath-seven-hour-2026-10-05/corpus/corridor-axis-profiles.json';out.write_text(json.dumps(dict(records=records,status='Exact finite corridor incidence profiles; no uniform singular-grid or doubling theorem yet'),indent=2)+'\n')
