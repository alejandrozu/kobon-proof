"""Finite exact checks of rational approximations to the Furedi-Palasti lines."""
import sys, math, json
from pathlib import Path
from fractions import Fraction as F

root = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(root / 'outputs' / 'kobon-extension'))
from exact_geometry import primitive, arrangement

data = []
for n in range(3, 61):
    lines = []
    for i in range(n):
        a = (2*i+1)*math.pi/n
        lines.append(primitive(tuple(F(str(x)) for x in
            (math.sin(a/2), math.cos(a/2), math.sin(3*a/2)))))
    ar = arrangement(lines)
    simple = len(ar['points']) == n*(n-1)//2 and all(len(s)==2 for s in ar['points'].values())
    assert simple
    data.append({'n': n, 'triangles': len(ar['triangles']), 'simple': simple, 'lines': lines})
    print(n, len(ar['triangles']), flush=True)
(Path(__file__).with_name('table_baseline.json')).write_text(json.dumps(data), encoding='utf-8')
