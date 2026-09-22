"""Reproducible search on the rational nodal-cubic line family.

Angles are only used to rank candidates. Every retained candidate is rounded in
the rational parameter t=tan(theta), not in unrelated line coefficients, then
checked by the independent exact adjacency counter. No floating count is a proof.
"""
from __future__ import annotations
import argparse, json, math, sys, time
from pathlib import Path
from fractions import Fraction
import numpy as np

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT / 'research/kobon-extension'))
from exact_geometry import arrangement, primitive

def triangles(theta):
    n = len(theta)
    # On line i the intersection coordinate is cos(3 theta_i) +
    # 2 cos(theta_i+2 theta_j). The first summand does not affect order.
    u = np.cos(theta[:, None] + 2*theta[None, :])
    np.fill_diagonal(u, np.inf)
    rows = np.argsort(u, axis=1)[:, :-1]
    a = np.broadcast_to(np.arange(n)[:, None], (n, n-2)).ravel()
    triples = np.stack((a, rows[:, :-1].ravel(), rows[:, 1:].ravel()), axis=1)
    triples.sort(axis=1)
    keys = triples[:, 0]*n*n + triples[:, 1]*n + triples[:, 2]
    keys, counts = np.unique(keys, return_counts=True)
    return int(np.count_nonzero(counts == 3))

def certify(theta, path, expected, metadata):
    n = len(theta)
    for denominator in (10**8, 10**12, 10**16):
        ts = [Fraction(float(math.tan(x))).limit_denominator(denominator) for x in theta]
        ls = [primitive((t*(1+t*t), 1+t*t, 3*t-t*t*t)) for t in ts]
        ar = arrangement(ls)
        count = len(ar['triangles'])
        simple = all(len(v) == 2 for v in ar['points'].values())
        if count == expected and simple:
            data = dict(n=n, triangle_count=count, simple=simple,
                        lines_frac=[[str(x) for x in l] for l in ls],
                        angles=list(map(float, theta)), rational_t=list(map(str, ts)),
                        verification='exact adjacency; direct-sign verification pending',
                        method='nodal cubic rational parameter', **metadata)
            path.write_text(json.dumps(data, indent=2)+'\n', encoding='utf-8')
            return count
    raise RuntimeError(f'exact rounding failed: float {expected}, exact {count}')

def main():
    p = argparse.ArgumentParser()
    p.add_argument('--n', type=int, required=True)
    p.add_argument('--seconds', type=float, default=300)
    p.add_argument('--seed', type=int, default=1)
    p.add_argument('--mode', choices=('local','global'), default='local')
    p.add_argument('--out', type=Path, required=True)
    args = p.parse_args()
    args.out.mkdir(parents=True, exist_ok=True)
    rng = np.random.default_rng(args.seed)
    n = args.n
    grid = np.arange(n)*math.pi/n
    eps = math.pi/(1000*n)
    phase = 1/6
    theta = grid + phase*math.pi/n
    best = triangles(theta)
    cert = args.out / f'n{n:03d}-{args.mode}-{args.seed}.json'
    certify(theta, cert, best, dict(seed=args.seed, mode=args.mode, proposals=0))
    start = time.monotonic()
    proposals = 0
    accepted = 0
    restarts = 0
    history = [dict(seconds=0, triangles=best)]
    print(json.dumps(dict(n=n, mode=args.mode, initial=best)), flush=True)
    while time.monotonic()-start < args.seconds:
        restarts += 1
        if args.mode == 'local':
            delta = rng.uniform(-1, 1, n)
            theta = grid + eps*delta
        else:
            theta = np.sort(rng.uniform(0, math.pi, n)) if restarts%4 == 0 else grid+rng.uniform(-.45,.45,n)*math.pi/n
        score = triangles(theta)
        stagnation = 0
        for step in range(max(1000, n*100)):
            proposals += 1
            i = int(rng.integers(n))
            trial = theta.copy()
            if args.mode == 'local':
                trial[i] = grid[i] + eps*rng.uniform(-1,1)
            else:
                lower = theta[i-1] if i else theta[-1]-math.pi
                upper = theta[i+1] if i<n-1 else theta[0]+math.pi
                trial[i] = rng.uniform(lower, upper)
            value = triangles(trial)
            temperature = max(.08, 1.2*(1-step/max(1000,n*100)))
            if value >= score or rng.random() < math.exp((value-score)/temperature):
                theta, score = trial, value
                accepted += 1
            if score > best:
                best = score
                elapsed = time.monotonic()-start
                certify(theta, cert, best, dict(seed=args.seed, mode=args.mode, proposals=proposals))
                history.append(dict(seconds=elapsed, triangles=best, proposals=proposals))
                print(json.dumps(dict(n=n, mode=args.mode, best=best, seconds=elapsed, proposals=proposals)), flush=True)
                stagnation = 0
            else:
                stagnation += 1
            if proposals%200 == 0 and time.monotonic()-start >= args.seconds:
                break
    report = dict(n=n, seed=args.seed, mode=args.mode, seconds=time.monotonic()-start,
                  proposals=proposals, accepted=accepted, restarts=restarts,
                  best=best, baseline=(n*(n-3)+2)//3, history=history,
                  limitations='bounded stochastic search; no optimality or priority claim')
    (args.out/f'n{n:03d}-{args.mode}-{args.seed}-report.json').write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps(report), flush=True)

if __name__ == '__main__':
    main()
