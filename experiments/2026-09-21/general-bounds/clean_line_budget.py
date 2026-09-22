"""Exact tests of the clean-line parity budget and triple-point fan bounds.

These checks support, but do not replace, the geometric proof in the report.
All line coefficients and intersections are exact integers/rationals.
"""
import collections,itertools,json,random,sys,time
from pathlib import Path
ROOT=Path(__file__).resolve().parents[3]
sys.path.insert(0,str(ROOT/'research/kobon-extension'))
from exact_geometry import arrangement,read_lines

def inspect(lines):
    ar=arrangement(lines);n=len(lines)
    edges=set()
    for row in ar['rows']:
        edges.update(frozenset(e)for e in zip(row,row[1:]))
    uses=collections.Counter(frozenset(e)for tri in ar['triangle_vertices']for e in itertools.combinations(tri,2))
    mult={p for p,inc in ar['points'].items()if len(inc)>=3}
    core_lines=set().union(*(ar['points'][p]for p in mult))if mult else set()
    ds={e for e,c in uses.items()if c==2}
    assert all(e&mult for e in ds)
    D1=sum(len(e&mult)==1 for e in ds);D2=sum(len(e&mult)==2 for e in ds)
    U=len(edges-set(uses));h=len(core_lines)
    P=sum(a[0]*b[1]==a[1]*b[0]for a,b in itertools.combinations(lines,2))
    local=[]
    if n%2==0 and P==0:
        for L in set(range(n))-core_lines:
            bad=[]
            rowset=set(ar['rows'][L])
            for e in edges:
                if len(e&rowset)==1 and uses[e]!=1:
                    bad.append(e)
            assert bad,('local parity failure',n,L,lines)
        assert n-h<=2*U+D1
    for p in mult:
        r=len(ar['points'][p])
        d1=sum(p in e and len(e&mult)==1 for e in ds)
        d2=sum(p in e and len(e&mult)==2 for e in ds)
        assert d1<=2*r-3,('cyclic fan failure',r,d1,d2,lines)
        assert d1+d2<=2*r
        if d2<=1:assert d1<=2*r-4,('general fan failure',r,d1,d2,lines)
        if r==3:
            assert d1<=3
            assert d1<3 or d2>=3
            local.append(dict(d1=d1,d2=d2))
    if n%2==0 and P==0 and len(mult)<=2:
        assert n*(n-2)-3*len(ar['triangles'])>=n//2-3
    weight=sum(2*len(ar['points'][p])**2-11*len(ar['points'][p])+6 for p in mult)
    if n%2==0 and P==0:
        assert 2*(n*(n-2)-3*len(ar['triangles']))>=n+weight
        if all(len(ar['points'][p])>=5 for p in mult):
            assert n*(n-2)-3*len(ar['triangles'])>=n//2
    return dict(n=n,T=len(ar['triangles']),h=h,U=U,D1=D1,D2=D2,
                multiple_points=len(mult),parallel_pairs=P,triple_point_fans=local,general_core_weight=weight)

if __name__=='__main__':
    start=time.monotonic();records=[]
    index=json.loads((ROOT/'verification/certificate-index.json').read_text())
    for rec in index:
        source=rec['sources'][0]
        row=inspect(read_lines(ROOT/source));row['source']=source;records.append(row)
    rng=random.Random(20260921)
    for n in range(4,23,2):
        for trial in range(30):
            ls=[(i,1,rng.randrange(-20,21))for i in range(n)]
            row=inspect(ls);row.update(source='random integer intercepts',trial=trial);records.append(row)
    for multiplicity in range(3,13):
        for trial in range(20):
            slopes=rng.sample(range(-100,101),2*multiplicity+4)
            ls=[(m,-1,0)for m in slopes[:multiplicity]]
            ls.extend((m,-1,m)for m in slopes[multiplicity:2*multiplicity])
            ls.extend((m,-1,rng.randrange(-10000,10001))for m in slopes[2*multiplicity:])
            row=inspect(ls);row.update(source='two high-multiplicity pencils',trial=trial);records.append(row)
    out=ROOT/'experiments/2026-09-21/general-bounds/clean-line-budget.json'
    out.write_text(json.dumps(dict(records=records,seconds=time.monotonic()-start,
        seed=20260921,checks='clean-line parity; triple fan; arbitrary r fan when d2<=1; cyclic d1<=2r-3; general weighted budget; no3/no4 simple-upper consequence; at most2-core-point upper consequence'),indent=2)+'\n')
    print(f'PASS {len(records)} arrangements; {time.monotonic()-start:.1f}s',flush=True)
