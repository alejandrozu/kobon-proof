"""Independent exact verification using the definition of an empty triangle.

Python standard library only. No numerical tolerances or external geometry code.
Usage: python verify_direct.py certificates/n051.json [...]
"""
import itertools
import json
import math
import sys
from fractions import Fraction
from pathlib import Path

def integer_line(values):
    values = [Fraction(x) for x in values]
    denominator = math.lcm(*(x.denominator for x in values))
    result = [x.numerator * (denominator // x.denominator) for x in values]
    divisor = math.gcd(*result)
    result = [x // divisor for x in result]
    if next(x for x in result if x) < 0:
        result = [-x for x in result]
    return tuple(result)

def verify(path):
    data = json.loads(Path(path).read_text())
    lines = [integer_line(x) for x in data['lines_frac']]
    assert len(set(lines)) == len(lines), 'Coincident lines'
    assert len(lines) == data['n']
    points = {}
    orientations = {}
    parallel = []
    for i, j in itertools.combinations(range(len(lines)), 2):
        a,b,c = lines[i]; d,e,f = lines[j]
        w = a*e-b*d
        if not w:
            parallel.append([i,j]); continue
        orientations[i,j] = 1 if w > 0 else -1
        p = [c*e-b*f, a*f-c*d, w]
        divisor = math.gcd(*p) * (1 if w > 0 else -1)
        points[i,j] = tuple(v//divisor for v in p)
    assert parallel == data.get('declared_parallel_pairs', [])
    assert not parallel, 'This verifier targets the nonparallel certificates in this package'
    # Sign bitsets implement the same open-interior test for all lines at once.
    # A cyclic determinant supplies the evaluations at the three pair-vertices.
    positive = {pair:0 for pair in points}
    negative = {pair:0 for pair in points}
    for i,j,k in itertools.combinations(range(len(lines)), 3):
        if (i,j) not in points or (i,k) not in points or (j,k) not in points:
            continue
        x,y,w = points[i,j]
        a,b,c = lines[k]
        value = a*x+b*y-c*w
        if not value:
            continue
        sij = 1 if value > 0 else -1
        determinant_sign = sij*orientations[i,j]
        sjk = determinant_sign*orientations[j,k]
        sik = -determinant_sign*orientations[i,k]
        for pair,index,sign in (((i,j),k,sij),((j,k),i,sjk),((i,k),j,sik)):
            if sign > 0:
                positive[pair] |= 1 << index
            else:
                negative[pair] |= 1 << index
    count = 0
    for i,j,k in itertools.combinations(range(len(lines)), 3):
        if (i,j) not in points or (i,k) not in points or (j,k) not in points:
            continue
        p,q,r = points[i,j],points[i,k],points[j,k]
        if p == q or p == r or q == r:
            continue
        positive_somewhere = positive[i,j] | positive[i,k] | positive[j,k]
        negative_somewhere = negative[i,j] | negative[i,k] | negative[j,k]
        count += not (positive_somewhere & negative_somewhere)
    expected = data['triangle_count']
    print(f'{Path(path).name}: n={len(lines)}, triangles={count}, expected={expected}, '
          f'{"PASS" if count == expected else "FAIL"}', flush=True)
    assert count == expected
    return dict(file=Path(path).name, n=len(lines), triangles=count, pass_check=True)

if __name__ == '__main__':
    for path in sys.argv[1:]:
        verify(path)
