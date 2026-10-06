"""Extract and verify a uniform tangent-grid 19-line seed from the public corpus.

This is an exact external certificate, not a Lean theorem.  The source is
Rohith Poola's rational realization of the Parpalak--Utkin 19-line seed.
All discovery rounding is fixed before Fraction-only interval checking.
"""
from pathlib import Path
from fractions import Fraction as F
import argparse, hashlib, importlib.util, itertools as it, json, sys, time

ROOT = Path(__file__).resolve().parents[3]
spec = importlib.util.spec_from_file_location("uniform49", ROOT / "experiments/2026-10-02/verify_uniform_grid49.py")
u = importlib.util.module_from_spec(spec)
spec.loader.exec_module(u)


def main():
    p = argparse.ArgumentParser()
    p.add_argument("--source", type=Path, default=ROOT / "work/openmath-rohith/kobon-triangles/doubled/n19_107_bp19_d10.json")
    p.add_argument("--out", type=Path, default=ROOT / "research/openmath-seven-hour-2026-10-05/corpus/uniform-seed19")
    args = p.parse_args()
    started = time.time()
    source = json.loads(args.source.read_text())
    # Reflect y, then shear x by 10y.  Both preserve the affine triangle cells.
    rows = sorted(((-F(c, a), 10 + F(b, a)) for a, b, c in source["lines"] if a), key=lambda row: row[0])
    assert len(rows) == 18
    denominator = 10**10
    v = [F(round(x * denominator), denominator) for a, x in rows]
    assert len(set(v)) == 18 and min(v) > 0 and v[8] > v[9]
    pi = u.dyadic(u.add(u.scale(u.atan_bound(F(1, 5)), 16), u.scale(u.atan_bound(F(1, 239)), -4)), 200)
    tangents = [u.dyadic(u.divide(u.trig_bound(u.scale(pi, F(k, 18)), True), u.trig_bound(u.scale(pi, F(k, 18)), False))) for k in range(1, 9)]
    # Our exact checker uses x-v*y=a; a is the actual x-axis crossing.
    a = [u.scale(x, -1) for x in reversed(tangents)] + [(F(0), F(0)), (F(0), F(0))] + tangents
    linear_coeff = [0] * 18
    linear_coeff[8], linear_coeff[9] = -1, 1
    radius = F(1, 100)
    signs = []
    minimum = None
    for i, j, k in it.combinations(range(18), 3):
        constant = u.add(u.add(u.scale(a[i], v[k] - v[j]), u.scale(a[j], v[i] - v[k])), u.scale(a[k], v[j] - v[i]))
        assert constant[0] > 0 or constant[1] < 0, (i, j, k, constant)
        sign = 1 if constant[0] > 0 else -1
        positive = u.scale(constant, sign)
        linear = sign * (linear_coeff[i] * (v[k] - v[j]) + linear_coeff[j] * (v[i] - v[k]) + linear_coeff[k] * (v[j] - v[i]))
        minimum = positive[0] if minimum is None else min(minimum, positive[0])
        if linear < 0:
            radius = min(radius, positive[0] / (-2 * linear))
        signs.append([i, j, k, sign])
    den = 1
    while F(1, den) > radius:
        den *= 10
    upper, epsilon = F(1, den), F(1, 2 * den)
    sample = [sum(x) / 2 for x in a]
    sample[8], sample[9] = -epsilon, epsilon
    lines = [(0, 1, 0)] + [u.primitive((1, -x, y)) for x, y in zip(v, sample)]
    ar = u.arrangement(lines)
    triangles = sorted(ar["triangles"])
    caps = [t for t in triangles if 0 in t]
    simple = len(ar["points"]) == 19 * 18 // 2 and all(len(support) == 2 for support in ar["points"].values())
    data = dict(n=19, triangle_count=len(triangles), Y0_triangles=len(caps), simple=simple,
        epsilon=str(epsilon), epsilon_upper=str(upper), reciprocal_slopes=[str(x) for x in v],
        lines_frac=[[str(x) for x in line] for line in lines], triangles=[list(x) for x in triangles],
        cap_triangles=[list(x) for x in caps], strict_old_triple_signs=signs,
        central_apex_positive=v[8] > v[9], trigonometric_intervals=dict(pi=u.encoded(pi), positive_tangents=[u.encoded(x) for x in tangents]),
        source=str(args.source.relative_to(ROOT)), source_sha256=hashlib.sha256(args.source.read_bytes()).hexdigest(),
        attribution="Parpalak--Utkin geometric seed; Rohith Poola rational realization; this script checks a uniform reflected/sheared chart",
        trust="Exact Fraction interval certificate; no Lean seed theorem claimed",
        zero_epsilon_determinant_margin=str(minimum), seconds=time.time() - started)
    args.out.mkdir(parents=True, exist_ok=True)
    (args.out / "uniform-seed.json").write_text(json.dumps(data, indent=2) + "\n")
    print(json.dumps({k: data[k] for k in ["n", "triangle_count", "Y0_triangles", "simple", "epsilon_upper", "central_apex_positive", "seconds"]}), flush=True)
    assert simple and len(triangles) == 107 and len(caps) == 17 and data["central_apex_positive"]


if __name__ == "__main__":
    main()
