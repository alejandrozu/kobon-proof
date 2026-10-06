"""Exact finite screens of two proposed global core/end resource inequalities.

First hypothesis is tested only at even orders. C counts singly-used plus
unused bounded edge endpoints at actual multiple points. Rc counts actual
unbounded line rays rooted at multiple points. No conjecture is proved here.
"""
from pathlib import Path
from fractions import Fraction as F
from collections import Counter
import itertools as it,json,random,re,sys,time
ROOT=Path(__file__).resolve().parents[3]
sys.path.insert(0,str(ROOT/"research/kobon-hybrid"))
from exact_geometry import arrangement,primitive


def ledger(lines):
    lines=list(map(primitive,lines));n=len(lines)
    if any(lines[i][0]*lines[j][1]==lines[i][1]*lines[j][0] for i,j in it.combinations(range(n),2)):return None
    ar=arrangement(lines);use=Counter();edges=set()
    for vertices in ar["rows"]:edges.update(frozenset(e) for e in zip(vertices,vertices[1:]))
    for tri in ar["triangle_vertices"]:use.update(frozenset(e) for e in it.combinations(tri,2))
    assert max(use.values(),default=0)<=2
    def core(p):return len(ar["points"][p])>=3
    D1=sum(u==2 and sum(core(p) for p in e)==1 for e,u in use.items())
    D2=sum(u==2 and sum(core(p) for p in e)==2 for e,u in use.items())
    assert all(u!=2 or any(core(p) for p in e) for e,u in use.items())
    U=len(edges)-len(use);C=sum(sum(core(p) for p in e) for e in edges if use[e]<=1)
    Rc=sum(core(vertices[0])+core(vertices[-1]) for vertices in ar["rows"])
    mult=[len(s) for s in ar["points"].values() if len(s)>=3]
    H=sum(r*(r-3) for r in mult);I=sum(mult);S=sum(r*(r-2) for r in mult)
    T=len(ar["triangles"]);deficit=n*(n-2)-3*T
    assert deficit==S+U-D1-D2
    assert 2*deficit==2*H+2*U-D1+C+Rc
    return dict(n=n,T=T,q=len(mult),multiplicities=dict(Counter(mult)),D1=D1,D2=D2,U=U,C=C,Rc=Rc,H=H,deficit=deficit,
                first_slack=2*U+D1+Rc-n if n%2==0 else None,second_slack=C+2*H+6-2*D1)


def main():
    start=time.time();cases=[];violations=[]
    def test(lines,source):
        r=ledger(lines)
        if r is None:return False
        r["source"]=source;cases.append(r)
        if (r["first_slack"] is not None and r["first_slack"]<0) or r["second_slack"]<0:
            violations.append(dict(r,lines_frac=[[str(c) for c in l] for l in lines]));return True
        return False
    base=ROOT/"work/openmath-rohith/kobon-triangles"
    rows=(base/"RESULTS.md").read_text().splitlines()
    for row in rows:
        m=re.match(r"\| (\d+) \| (\d+) \|",row)
        if not m:continue
        n=int(m.group(1));path=base/f"submissions/n{n}/solution.json"
        if not path.exists():continue
        lines=json.loads(path.read_text())["lines"]
        if test([(a,b,-c) for a,b,c in lines],str(path.relative_to(ROOT))):break
    if not violations:
        catalog=json.loads((ROOT/"manuscripts/2026-10-03/long/generated/certificate-catalog.json").read_text())
        for record in catalog:
            if record["n"]>70:continue
            source=record["sources"][0];raw=json.loads((ROOT/source).read_text())
            if test(raw["lines_frac"],source):break
    if not violations:
        rng=random.Random(847)
        for trial in range(80):
            n=rng.choice([8,10,12,14,16,18,20]);centers=[(rng.randint(-5,5),rng.randint(-5,5)) for _ in range(rng.randint(1,5))]
            slopes=rng.sample(range(-50,51),n);lines=[]
            for m in slopes:
                x,y=rng.choice(centers);lines.append((m,-1,m*x-y))
            if test(lines,f"Random exact pencil mixture, seed847 trial{trial}"):break
    out=ROOT/"research/openmath-seven-hour-2026-10-05/corpus/global-token-sanity.json"
    result=dict(passed=not violations,first="even n<=2U+D1+Rc",second="2D1<=C+2sum r(r-3)+6",
        status="Bounded exact sanity check, no global proof",cases=cases,violations=violations,seconds=time.time()-start)
    out.write_text(json.dumps(result,indent=2)+"\n")
    print(json.dumps(dict(tested=len(cases),violations=violations,seconds=result["seconds"])),flush=True)


if __name__=="__main__":main()
