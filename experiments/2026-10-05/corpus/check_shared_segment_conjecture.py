"""Exact counterexamples to the corpus's auxiliary D <= 2t rule.

The even-order conjectured upper bound is a separate statement and is not
refuted here.  D counts all elementary edges shared by two triangle cells.
Our line convention is a*x+b*y=c.
"""
from pathlib import Path
from collections import Counter
from fractions import Fraction as F
import hashlib, itertools as it, json, sys

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT / "research/kobon-hybrid"))
from exact_geometry import arrangement, intersection, primitive


def ledger(lines):
    ar = arrangement(lines)
    triples = sum(len(s) == 3 for s in ar["points"].values())
    used = Counter()
    for i, j, k in ar["triangles"]:
        p, q, r = intersection(lines[i], lines[j]), intersection(lines[i], lines[k]), intersection(lines[j], lines[k])
        used.update([frozenset((p, q)), frozenset((p, r)), frozenset((q, r))])
    assert max(used.values()) <= 2
    double = sum(c == 2 for c in used.values())
    parallel = sum(lines[i][0]*lines[j][1] == lines[i][1]*lines[j][0] for i, j in it.combinations(range(len(lines)), 2))
    return dict(n=len(lines), triangles=len(ar["triangles"]), triples=triples,
                shared_segments=double, parallel_pairs=parallel, excess=double-2*triples,
                multiple_points=sum(len(s)>=3 for s in ar["points"].values()),
                multiplicity_profile=dict(Counter(len(s) for s in ar["points"].values())),
                lines_frac=[list(x) for x in lines], triangle_triples=[list(x) for x in sorted(ar["triangles"])])


def verify(m):
    lines = [(1, 0, i) for i in range(m)] + [(0, 1, j) for j in range(m)] + [(1, 1, k) for k in range(1, 2*m-2)]
    result = ledger(lines)
    assert max(map(int, result["multiplicity_profile"])) <= 3
    return dict(m=m, **result)


def projective(m):
    old=verify(m)
    epsilon=F(1,100*m)
    # X=x/(1-eps*(x+2y)), Y=y/(1-eps*(x+2y)).
    lines=[primitive((F(a)+epsilon*c,F(b)+2*epsilon*c,c)) for a,b,c in old["lines_frac"]]
    result=ledger(lines)
    assert result["parallel_pairs"] == 0
    assert set(map(tuple,old["triangle_triples"])) <= set(map(tuple,result["triangle_triples"]))
    assert result["shared_segments"] >= old["shared_segments"]
    assert result["multiple_points"] == m*m+1
    return dict(m=m, epsilon=str(epsilon), retained_old_triangles=old["triangles"], **result)


if __name__ == "__main__":
    cases = [verify(m) for m in range(3, 11)]
    transformed = [projective(m) for m in range(4, 11)]
    out = ROOT / "research/openmath-seven-hour-2026-10-05/corpus/shared-segment-counterexamples.json"
    out.parent.mkdir(parents=True, exist_ok=True)
    result = dict(passed=True, claim_refuted="D <= 2t without an exclusion of parallel classes",
                  claim_not_refuted="even-order generalized Blanc upper bound",
                  trust="Exact integer geometry, external checker; not a Lean theorem", cases=cases,
                  projective_no_parallel_cases=transformed,
                  scope_note="Transformed cases have higher-multiplicity points and do not refute a rule restricted to double/triple intersections")
    out.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps([{k:r[k] for k in ["m", "n", "triangles", "triples", "shared_segments", "parallel_pairs", "excess"]} for r in cases]))
    print(json.dumps([{k:r[k] for k in ["m", "n", "triangles", "triples", "multiple_points", "shared_segments", "parallel_pairs", "multiplicity_profile"]} for r in transformed]))
