"""Exact, reproducible test of repeated exterior addition to the saved 49 seed.

Records all coordinates, sector profiles, and deterministic tie breaking. The
generated Lean file checks finite profile arithmetic; its geometric provenance
is verified by this exact program, not silently asserted as a Lean theorem.
"""
from pathlib import Path
from fractions import Fraction
import hashlib
import json
import sys

ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'research/kobon-extension'))
from boundary_extension import arrangement,exterior_choices,cyclic_data

source=ROOT/'research/finite-table/simple-049.json'
data=json.loads(source.read_text())
lines=[tuple(Fraction(z) for z in row) for row in data['lines_frac']]
states=[]
previous_triangles=None
previous_count=None
for step in range(5):
    ar=arrangement(lines)
    n=len(lines)
    triangles=set(ar['triangles'])
    assert len(ar['points'])==n*(n-1)//2
    assert all(len(ls)==2 for ls in ar['points'].values())
    if previous_triangles is not None:
        assert previous_triangles <= triangles
        assert len(triangles)==previous_count
    boundary,profile=cyclic_data(ar)
    choices=exterior_choices(ar)
    gain,line=choices[0]
    assert max(profile)==gain
    assert len(set(boundary))==len(boundary)
    assert sum(profile)==(n-1)*len(boundary)
    states.append(dict(n=n,triangles=len(triangles),wedges=len(boundary),
        maximum_exterior_gain=gain,requested_gain=n//2,
        wedge_starts=boundary,profile=profile,chosen_sector=profile.index(gain),
        added_line=list(line),lines=[[str(x) for x in row] for row in ar['lines']]))
    print(f'{n}: {len(triangles)} triangles, {len(boundary)} wedges, maximum exterior gain {gain}',flush=True)
    previous_triangles=triangles
    previous_count=len(triangles)+gain
    lines=lines+[line]

dest=ROOT/'experiments/2026-09-20/successor-49'
dest.mkdir(parents=True,exist_ok=True)
result=dict(source=source.relative_to(ROOT).as_posix(),source_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),
    tie_breaking='exterior_choices sorts (count, primitive integer line) in reverse lexicographic order; take first',
    scope='Exact finite experiment. Failure of this exterior route does not refute the recurrence for maxima or interior/rebuilt constructions.',
    states=states)
(dest/'chain.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8',newline='\n')
body='''import Kobon.BoundaryExtension

/-! Finite sector-profile arithmetic for the exact 49-line successor experiment.
The map from these arrays to the real arrangements is independently computed
by audit_successor_chain.py; it is not an additional premise hidden in Lean. -/
namespace Kobon.Iteration49
open KobonBoundary
set_option maxRecDepth 100000
set_option maxHeartbeats 0

'''
for row in states:
    n=row['n'];gain=row['maximum_exterior_gain']
    body+=f'def boundary_{n} : Finset (ZMod {2*n}) := '+'{'+','.join(map(str,row['wedge_starts']))+'}\n\n'
    body+=f'theorem profile_bound_{n} : ∀ j : ZMod {2*n}, capCount {n-1} boundary_{n} j ≤ {gain} := by\n  decide +kernel\n\n'
    body+=f'theorem profile_attains_{n} : capCount {n-1} boundary_{n} {row["chosen_sector"]}={gain} := by\n  decide +kernel\n\n'
body+='#print axioms profile_bound_50\n#print axioms profile_attains_50\nend Kobon.Iteration49\n'
(ROOT/'Kobon/Iteration49.lean').write_text(body,encoding='utf-8',newline='\n')
