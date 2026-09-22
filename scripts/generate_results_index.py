"""Current strongest saved coordinate values, with links and attribution scope."""
from pathlib import Path
import json

ROOT=Path(__file__).resolve().parents[1]
records=json.loads((ROOT/'verification/certificate-index.json').read_text())
oeis={r['n']:r['explicit_lower'] for r in json.loads((ROOT/'evidence/oeis-observations.json').read_text())['rows']}
body='''# Verified result index

The strongest proved all-order function is `Universal.bound`: the maximum of
`G(n)=floor(n(n-3)/3)+1+(n mod 2)` for `n>=4` and the finite envelope below.
Use zero below three and one at three. The generic construction uses only
standard logical axioms; finite coordinate checks use native evaluation.

The table records the strongest **saved coordinate witnesses**, not an
exhaustive global record table or a list of original discoveries. Maiorana,
Parpalak–Utkin and earlier researchers retain attribution for their inputs.
The linked source certificates and evidence snapshots preserve provenance.
The OEIS column records the explicit table as observed on20September2026;
an omitted entry is not evidence of novelty.

The corresponding aliases are `Results.best_classical_NNN` and
`Results.best_simple_NNN`. Historical `Results.classical_NNN` and
`Results.simple_NNN` still verify the earlier materialized3–60table, while
`Results.earlier_NNN` retains every inequality in the original inventory.
Consult [FORMALIZATION.md](FORMALIZATION.md), the
[cumulative review](research/six-hour-2026-09-21/RESEARCH_REVIEW.md), and
[build results](verification/lean-summary.json) for scope and verification.

| n | Saved simple bound | Saved classical bound | Explicit OEIS lower | Strongest classical coordinate witness |
|---:|---:|---:|---:|---|
'''
for n in sorted({d['n'] for d in records}):
    ds=[d for d in records if d['n']==n]
    d=max(ds,key=lambda d:d['triangles'])
    simple=max((x['triangles'] for x in ds if x['simple']),default=None)
    o=oeis.get(n)
    body+=f'| {n} | {simple if simple is not None else "—"} | {d["triangles"]} | {o if o is not None else "—"} | [coordinates]({d["sources"][0]}) · [Lean]({d["lean_source"]}) |\n'
body+='''
The three earlier OEIS-attributed Zarzuelo values28:238,30:275and34:357
remain independently certified. Some newer values in this catalog reproduce
published nonsimple constructions; this improves the repository's coverage
without making them our numerical discoveries. Current upper bounds and
priority claims require the separate source and hypothesis audit.
'''
body=body.replace('on20September2026','on 20 September 2026').replace('materialized3–60table','materialized 3–60 table').replace('values28:238,30:275and34:357','values 28:238, 30:275 and 34:357')
(ROOT/'RESULTS.md').write_text(body,encoding='utf-8')
print('Wrote current coordinate result index.')
