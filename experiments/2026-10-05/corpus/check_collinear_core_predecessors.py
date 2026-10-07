"""Exact deletion of a common core line in published even nonsimple records.

Recovered predecessor faces are counted separately from removed faces; the
net gain must not be confused with the number of triangles incident to the line.
"""
from pathlib import Path
from fractions import Fraction as F
from collections import Counter
import itertools as it,json,sys,time
ROOT=Path(__file__).resolve().parents[3];sys.path.insert(0,str(ROOT/'research/kobon-hybrid'));sys.path.insert(0,str(Path(__file__).resolve().parent))
from exact_geometry import arrangement
from check_global_token_hypotheses import ledger

if __name__=='__main__':
    started=time.time();records=[]
    sources=[(n,ROOT/f'research/six-hour-2026-09-21/general-bounds/parpalak-utkin-current/certificate-{n:03d}.json') for n in [8,14,20,26,32,38,50]]
    sources += [(50,ROOT/'work/openmath-rohith/kobon-triangles/submissions/n50/solution.json')]
    sources += [(14,ROOT/f'research/six-hour-2026-09-21/general-bounds/maiorana14/certificate-{i:02d}.json') for i in range(1,16)]
    for n,source in sources:
        raw=json.loads(source.read_text());lines=[tuple(map(F,l)) for l in raw['lines_frac']] if 'lines_frac' in raw else [(F(a),F(b),-F(c)) for a,b,c in raw['lines']];ar=arrangement(lines);cores=[(p,s) for p,s in ar['points'].items() if len(s)>=3];common=set.intersection(*(set(s) for p,s in cores)) if cores else set();old=set(tuple(sorted(t)) for t in ar['triangles'])
        record=dict(n=n,T=len(old),source=str(source.relative_to(ROOT)),ledger=ledger(lines),cores=[dict(point=list(map(str,p)),lines=sorted(s),multiplicity=len(s)) for p,s in cores],common_lines=sorted(common),deletions=[])
        for removed in sorted(common):
            ids=[i for i in range(n) if i!=removed];candidate=[lines[i] for i in ids];prev=arrangement(candidate);new=set(tuple(sorted(ids[i] for i in t)) for t in prev['triangles']);removed_count=sum(removed in t for t in old);retained={t for t in old if removed not in t};recovered=new-retained
            assert retained<=new
            a,b,c=lines[removed];sides=Counter((a*p[0]+b*p[1]-c*p[2]>0)-(a*p[0]+b*p[1]-c*p[2]<0) for p in prev['points'])
            r=dict(removed_line=removed,predecessor_n=n-1,predecessor_T=len(new),predecessor_simple=len(prev['points'])==(n-1)*(n-2)//2 and all(len(s)==2 for s in prev['points'].values()),old_triangles_on_line=removed_count,retained_old=len(retained),recovered_predecessor_faces=len(recovered),net_gain=len(old)-len(new),predecessor_vertex_side_census=dict(sides),supporting_convex_hull=not(sides[-1] and sides[1]),recovered_triangles=sorted(recovered))
            record['deletions'].append(r)
        records.append(record);print(json.dumps(record),flush=True)
    out=ROOT/'research/openmath-seven-hour-2026-10-05/corpus/collinear-core-predecessors.json';out.write_text(json.dumps(dict(passed=True,records=records,seconds=time.time()-started,status='Exact external deletion/recovery census; no scalable non-strict extension theorem yet'),indent=2)+'\n')
