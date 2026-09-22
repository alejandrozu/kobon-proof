"""Exact six-line counterexample to an incidence reading of a local claim.

This does not refute any global Kobon upper bound. It checks the triangle-plus-
medians example against the literal local wording in Clement--Bader Lemma 1(3).
"""
import collections,itertools,json,sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[3]
sys.path.insert(0,str(ROOT/'research/kobon-extension'))
from exact_geometry import arrangement
from clean_line_budget import inspect

lines=[(1,0,0),(0,1,0),(1,1,3),(1,-1,0),(2,1,3),(1,2,3)]
ar=arrangement(lines)
uses=collections.Counter(frozenset(e)for tri in ar['triangle_vertices']for e in itertools.combinations(tri,2))
shared=[e for e,c in uses.items()if c==2]
center=(1,1,1)
assert len(ar['triangles'])==6 and len(ar['points'][center])==3
incident=[e for e in shared if center in e]
assert len(incident)==6
local=[]
for p,inc in ar['points'].items():
    if len(inc)<3:continue
    es=[e for e in shared if p in e]
    d1=sum(len(ar['points'][next(iter(e-{p}))])==2 for e in es)
    local.append(dict(point=p,multiplicity=len(inc),shared_incident=len(es),d1=d1,d2=len(es)-d1))
out=ROOT/'research/six-hour-2026-09-21/general-bounds/shared-fan-six-lines.json'
out.write_text(json.dumps(dict(n=6,triangle_count=6,lines_frac=lines,
    source='Triangle with vertices (0,0),(3,0),(0,3), together with its three medians.',
    claim_scope='Counterexample only to a literal local incidence bound of two shared sides per multiple point; no global upper theorem is refuted.',
    triangles=ar['triangles'],core_fans=local,budget=inspect(lines)),indent=2)+'\n')
print(out)
print(json.dumps(local))
