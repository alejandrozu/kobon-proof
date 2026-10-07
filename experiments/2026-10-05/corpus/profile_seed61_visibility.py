"""Exact exhaustive direction profiles of contestant61 variants.

Only the61 admissible normal sectors and their opposites need checking.
Allowed endpoint derivative signs of every exterior wedge are precomputed
once from integer determinants.  No numerical angle or tolerance is used.
"""
from pathlib import Path
from fractions import Fraction as F
import hashlib,itertools as it,json,sys,time
ROOT=Path(__file__).resolve().parents[3]
sys.path.insert(0,str(ROOT/"research/kobon-hybrid"))
from exact_geometry import arrangement,primitive


def sign(x):return (x>0)-(x<0)
def det(l,m):return l[0]*m[1]-l[1]*m[0]


def profile(path):
    started=time.time();raw=json.loads(path.read_text())
    lines=[primitive((a,b,-c)) for a,b,c in raw["lines"]]
    n=len(lines);ar=arrangement(lines)
    assert all(len(s)==2 for s in ar["points"].values()) and len(ar["points"])==n*(n-1)//2
    determinants={(i,j):det(lines[i],lines[j]) for i,j in it.product(range(n),repeat=2)}
    assert all(determinants[i,j]!=0 for i,j in it.combinations(range(n),2))
    allowed=[]
    for i,j in it.combinations(range(n),2):
        ai,bi,ci=lines[i];aj,bj,cj=lines[j];d=determinants[i,j]
        x,y=ci*bj-bi*cj,ai*cj-ci*aj
        tests=[]
        for r,(a,b,c) in enumerate(lines):
            if r in [i,j]:continue
            tests.append((sign((a*x+b*y-c*d)*d),sign(determinants[r,i]),sign(determinants[r,j])))
        for si,sj in it.product([-1,1],repeat=2):
            if all(di*si==dj*sj and (e==0 or e==di*si) for e,di,dj in tests):
                allowed.append((i,j,si,sj))
    critical=sorted({F(b,a) for a,b,c in lines if a})
    samples=[critical[0]-1]+[(a+b)/2 for a,b in zip(critical,critical[1:])]+[critical[-1]+1]
    right=max((F(c,a),i) for i,(a,b,c) in enumerate(lines) if a)[1]
    left=min((F(c,a),i) for i,(a,b,c) in enumerate(lines) if a)[1]
    reports=[]
    for b in samples:
        for a,w_b in [(F(1),b),(F(-1),-b)]:
            directions=[sign(a*y-w_b*x) for x,y,z in lines]
            assert all(directions)
            pairs=[(i,j) for i,j,si,sj in allowed if directions[i]==si and directions[j]==sj]
            reports.append(dict(normal=[str(a),str(w_b)],visible_count=len(pairs),
                rightmost_pair=(0,right) in pairs,leftmost_pair=(0,left) in pairs,
                visible_pairs=pairs))
    max_count=max(r["visible_count"] for r in reports)
    return dict(source=str(path.relative_to(ROOT)),source_sha256=hashlib.sha256(path.read_bytes()).hexdigest(),
        n=n,triangles=len(ar["triangles"]),simple=True,normal_sectors=len(reports),
        max_visible=max_count,max_combined=len(ar["triangles"])+max_count,
        max_positive_a=max(r["visible_count"] for r in reports if F(r["normal"][0])>0),
        best_reports=[r for r in reports if r["visible_count"]==max_count],
        reports=reports,seconds=time.time()-started)


if __name__=="__main__":
    base=ROOT/"work/openmath-rohith/kobon-triangles/bases"
    results=[profile(base/name) for name in ["n61_1189_base31.json","n61_1190_base31.json"]]
    out=ROOT/"research/openmath-seven-hour-2026-10-05/corpus/seed61-variant-visibility.json"
    out.write_text(json.dumps(dict(passed=True,trust="Exact external direction-sector audit; not yet a Lean seed theorem",results=results),indent=2)+"\n")
    print(json.dumps([{k:r[k] for k in ["n","triangles","max_visible","max_positive_a","max_combined","normal_sectors","seconds"]} for r in results]))
