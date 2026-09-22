"""Exact segment-use and multiplicity budget for saved rational arrangements."""
import collections,itertools,json,sys,time
from pathlib import Path
ROOT=Path(__file__).resolve().parents[3]
sys.path.insert(0,str(ROOT/'research/kobon-extension'))
from exact_geometry import arrangement,read_lines

def budget(path):
    ar=arrangement(read_lines(path));n=len(ar['lines'])
    edges=set()
    for row in ar['rows']:
        edges.update(frozenset(e)for e in zip(row,row[1:]))
    uses=collections.Counter(frozenset(e)for tri in ar['triangle_vertices']for e in itertools.combinations(tri,2))
    assert set(uses)<=edges and all(u in (1,2)for u in uses.values())
    U=len(edges-set(uses));D=sum(u==2 for u in uses.values())
    mult=collections.Counter(map(len,ar['points'].values()))
    P=sum(a[0]*b[1]==a[1]*b[0]for a,b in itertools.combinations(ar['lines'],2))
    q=sum(bool(row)for row in ar['rows'])
    S=sum(r*(r-2)*t for r,t in mult.items())
    T=len(ar['triangles']);defect=n*(n-2)-3*T
    assert len(edges)==n*(n-1)-2*P-S-q
    assert 3*T==len(edges)-U+D
    assert defect==2*P+S+q-n+U-D
    return dict(source=str(path.relative_to(ROOT)),n=n,triangles=T,parallel_pairs=P,
                intersection_multiplicities=dict(sorted(mult.items())),
                bounded_segments=len(edges),unused_segments=U,double_used_segments=D,
                concurrency_segment_penalty=S,defect=defect,
                exact_identity_verified=True)

if __name__=='__main__':
    start=time.monotonic()
    index=json.loads((ROOT/'verification/certificate-index.json').read_text())
    records=[budget(ROOT/rec['sources'][0])for rec in index]
    out=ROOT/'experiments/2026-09-21/general-bounds/multiplicity-budget.json'
    out.write_text(json.dumps(dict(records=records,seconds=time.monotonic()-start,
        formula='n(n-2)-3T = 2P + sum_r r(r-2)t_r + q-n + U-D'),indent=2)+'\n')
    for r in records:
        if r['concurrency_segment_penalty']:
            print(json.dumps(r),flush=True)
    print(f'PASS: {len(records)} exact budgets; {time.monotonic()-start:.1f}s',flush=True)
