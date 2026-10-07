"""Exact sign-combinatorial shared-edge audit for concurrent FP phase zero.

L_i=(sin(pi*i/n),cos(pi*i/n),sin(3*pi*i/n)), with a*x+b*y=c.
Pair determinants are nonzero. A sorted triple is concurrent exactly when
i+j+k=0 mod n, so all multiple points have multiplicity three. No numeric
coordinates are used by the shared-edge count.
"""
from pathlib import Path
from collections import Counter
import hashlib, itertools as it, json

ROOT=Path(__file__).resolve().parents[3]


def vertex(n,i,j):
    k=(-i-j)%n
    return tuple(sorted({i,j,k})) if k!=i and k!=j else tuple(sorted((i,j)))


def run(n):
    pos={p:0 for p in it.combinations(range(n),2)}
    neg={p:0 for p in pos}
    for i,j,k in it.combinations(range(n),3):
        total=i+j+k
        if total%n==0: continue
        s=1 if (total//n)%2==0 else -1
        for pair,index,sign in (((i,j),k,s),((i,k),j,-s),((j,k),i,s)):
            (pos if sign>0 else neg)[pair]|=1<<index
    triangles=[]
    for i,j,k in it.combinations(range(n),3):
        if (i+j+k)%n==0:continue
        if not ((pos[i,j]|pos[i,k]|pos[j,k]) & (neg[i,j]|neg[i,k]|neg[j,k])):
            triangles.append((i,j,k))
    uses=Counter()
    for i,j,k in triangles:
        p,q,r=vertex(n,i,j),vertex(n,i,k),vertex(n,j,k)
        assert len({p,q,r})==3
        uses.update([tuple(sorted((p,q))),tuple(sorted((p,r))),tuple(sorted((q,r)))])
    assert max(uses.values(),default=0)<=2
    points={vertex(n,i,j) for i,j in it.combinations(range(n),2)}
    triples=sum(len(p)==3 for p in points)
    shared=sum(u==2 for u in uses.values())
    ordinary_shared=sum(u==2 and sorted(map(len,edge))==[2,3] for edge,u in uses.items())
    core_shared=sum(u==2 and all(len(p)==3 for p in edge) for edge,u in uses.items())
    assert ordinary_shared+core_shared==shared
    return dict(n=n,triangles=len(triangles),triple_points=triples,parallel_pairs=0,
                shared_segments=shared,ordinary_shared=ordinary_shared,core_shared=core_shared,
                excess=shared-2*triples,
                canonical_triangle_list=triangles if shared>2*triples else None)


if __name__=="__main__":
    rows=[run(n) for n in list(range(4,81))+[99,120,195]]
    result=dict(passed=True,claim_tested="D<=2t, no parallels, all multiplicities at most three",
                method="Exact chirotope signs and canonical vertex supports, no floating geometry",
                original_counter="experiments/2026-09-20/audit_fp_nonsimple.py",
                original_counter_sha256=hashlib.sha256((ROOT/"experiments/2026-09-20/audit_fp_nonsimple.py").read_bytes()).hexdigest(),
                rows=rows,counterexamples=[r for r in rows if r["excess"]>0])
    out=ROOT/"research/openmath-seven-hour-2026-10-05/corpus/fp-shared-rule.json"
    out.parent.mkdir(parents=True,exist_ok=True)
    out.write_text(json.dumps(result,indent=2)+"\n")
    print(json.dumps(dict(cases=len(rows),counterexample_count=len(result["counterexamples"]),
        selected=[{k:r[k] for k in ["n","triangles","triple_points","shared_segments","ordinary_shared","core_shared","excess"]} for r in rows if r["n"] in [8,9,18,39,120,195]])))
