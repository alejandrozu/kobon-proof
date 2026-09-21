"""Recheck exact examples and optionally the deterministic 560-case test set.

Usage: python verify_all.py [--regression]
Python standard library only. No network, floats or third-party packages.
"""
from boundary_extension import *
from verify_direct import verify
import random, sys

root=Path(__file__).resolve().parent
results=[];profiles={}
for path in sorted((root/'certificates').glob('*.json')):
    direct=verify(path)
    data=json.loads(path.read_text());ls=[primitive(x) for x in data['lines_frac']]
    ar=arrangement(ls)
    assert len(ar['triangles'])==data['triangle_count']
    assert len(ar['points'])==data['n']*(data['n']-1)//2
    assert all(len(s)==2 for s in ar['points'].values())
    profile=check(ls)
    profiles[path.stem]=profile
    results.append(dict(file=path.name,n=data['n'],triangles=data['triangle_count'],
        direct_count=direct['triangles'],adjacency_count=len(ar['triangles']),simple=True))

for prefix,sequence in [('chain',[5,6,7]),('chain',[19,20,21]),('alternation',[5,6])]:
    for n,m in zip(sequence,sequence[1:]):
        old=arrangement(read_lines(root/'certificates'/f'{prefix}_{n}.json'))
        new=arrangement(read_lines(root/'certificates'/f'{prefix}_{m}.json'))
        assert new['lines'][:n]==old['lines']
        assert set(old['triangles'])<=set(new['triangles'])
assert profiles['chain_7']['actual_gain']==2
assert profiles['chain_20']['actual_gain']==9

checked=0
if '--regression' in sys.argv:
    rng=random.Random(20092026)
    for n in range(3,31):
        for trial in range(20):
            while True:
                ls=[(i,-1,rng.randrange(-100000,100001)) for i in range(n)]
                ar=arrangement(ls)
                if len(ar['points'])==n*(n-1)//2 and all(len(s)==2 for s in ar['points'].values()):break
            check(ls);checked+=1

report=dict(examples=results,boundary_profiles=profiles,
    preserved_triangle_chains=[[5,6,7],[19,20,21]],
    deterministic_regression_cases=checked,all_checks_passed=True,
    scope='Exact finite checks; the infinite geometric proof is in manuscript.md')
(root/'verification.json').write_text(json.dumps(report,indent=2),encoding='utf8')
print(f'PASS: {len(results)} certificates counted by two methods; old triangles preserved; {checked} regression cases.')
