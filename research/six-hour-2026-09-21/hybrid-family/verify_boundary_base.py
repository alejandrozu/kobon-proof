"""Exact rational interval check for a whole 21-line BBL boundary family.

The trigonometric constants are enclosed by the pre-existing Machin/Taylor
interval implementation.  All expressions for a triple are affine in epsilon;
the two endpoints therefore certify every 0 < epsilon <= 1/100000.  This is
a Python-assisted analytic certificate, not a Lean theorem.
"""
from pathlib import Path
import json
import sys

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT / "research/kobon-hybrid"))
from verify_seed import I, F, V, EPS, grid, tan_pi


def det(l, m):
    return l[0] * m[1] - l[1] * m[0]


def eval_vertex(r, l, m):
    return (r[0] * (l[2] * m[1] - l[1] * m[2])
            + r[1] * (l[0] * m[2] - l[2] * m[0])
            - r[2] * det(l, m))


def build(epsilon):
    old = [(I(0), I(1), I(0))]
    old += [(I(1), I(-v), a) for a, v in zip(grid(epsilon), V)]
    positive = [tan_pi(k, 20) for k in range(1, 10, 2)]
    bb = [-x for x in positive[::-1]] + positive
    kappa = F(2, 3 * 10**10)  # m_min / 10^10, m_min = 2/3.
    mm = [kappa * (2*b/(1+b*b) + I(1)/(10**6*b)) for b in bb]
    return old + [(m, I(-1), m*b) for m, b in zip(mm, bb)]


VISIBLE = [(0,20), (1,3), (2,4), (5,7), (6,8), (10,13),
           (11,15), (12,14), (16,19), (17,18)]


def check(output=None):
    endpoints = [build(F(0)), build(EPS)]
    w = (I(10), I(-13), I(0))
    sign_checks = 0
    margin = F(1)
    for i, j in VISIBLE:
        for r in range(21):
            ds = [det(endpoints[0][r], endpoints[0][i]),
                  det(endpoints[0][r], endpoints[0][j])]
            den = [det(w, endpoints[0][i]), det(w, endpoints[0][j])]
            signs = [0 if r == p else a.sign()*b.sign()
                     for p,a,b in zip((i,j),ds,den)]
            assert all(x.sign() for x in den)
            assert not (1 in signs and -1 in signs), (i,j,r,signs)
            s = next(x for x in signs if x)
            if r in (i,j):
                continue
            for lines in endpoints:
                d = det(lines[i], lines[j])
                value = eval_vertex(lines[r], lines[i], lines[j])
                assert d.sign() and value.sign()
                assert value.sign()*d.sign() == s, (i,j,r,s)
                margin = min(margin,abs(value.lo),abs(value.hi))
                sign_checks += 1
    for line in endpoints[0]:
        assert det(line,w).sign()
    report = dict(
        epsilon_interval="0 < epsilon <= 1/100000",
        lines=21, visible_pairs=[list(p) for p in VISIBLE],
        visible_pair_count=len(VISIBLE), normal=[10,-13],
        non_supporting_endpoint_checks=sign_checks,
        minimum_homogeneous_evaluation_margin=str(margin),
        result="PASS: every listed pair is visible for the entire parameter interval",
        mathematical_basis="Triples are affine in epsilon; all endpoint signs are certified by outward-rounded rational intervals",
        trust="Python interval certificate plus Machin identity and Taylor remainder bounds; not Lean",
    )
    if output:
        Path(output).write_text(json.dumps(report,indent=2)+"\n",encoding="utf-8")
    print(json.dumps(report,indent=2))
    return report


if __name__ == "__main__":
    check(Path(__file__).with_name("boundary-base-verification.json"))
