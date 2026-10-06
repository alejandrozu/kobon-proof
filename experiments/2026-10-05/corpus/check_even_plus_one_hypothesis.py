"""Bounded sanity test of a general-multiplicity even upper conjecture.

This does not prove an upper bound.  It checks known exact counts and
literature values against6T<=n(2n-5)+6, keeping their source scopes separate.
"""
from pathlib import Path
import json
ROOT=Path(__file__).resolve().parents[3]
OUT=ROOT/"research/openmath-seven-hour-2026-10-05/corpus"


if __name__=="__main__":
    cases=[]
    inventory=json.loads((OUT/"source-inventory.json").read_text())
    for r in inventory["point_comparison"]:
        cases.append(dict(n=r["n"],T=r["contestant_point_count"],source="Rohith66 point-count table; independent archive recounts, not rerun by this script"))
    catalog=json.loads((ROOT/"manuscripts/2026-10-03/long/generated/certificate-catalog.json").read_text())
    for r in catalog:cases.append(dict(n=r["n"],T=r["triangles"],source=r["module"]))
    for r in json.loads((OUT/"fp-shared-rule.json").read_text())["rows"]:
        cases.append(dict(n=r["n"],T=r["triangles"],source="Exact phase-zero FP chirotope checker"))
    # Classical published finite benchmark values that exceed or meet a
    # simple-arrangement upper floor are relevant scope tests.
    for n,T in [(6,7),(8,15),(10,25),(12,38),(14,54),(16,72),(18,93),(20,117),(22,143),(24,172),(26,203),(28,238),(30,275),(32,311),(34,357),(36,397),(38,450),(44,608),(46,667),(48,721),(50,792),(52,850),(54,927),(56,990),(60,1141)]:
        cases.append(dict(n=n,T=T,source="Classical finite benchmark/literature count; no new priority assertion"))
    tested=[]
    for r in cases:
        if r["n"]%2 or r["n"]<4:continue
        n,T=r["n"],r["T"];slack=n*(2*n-5)+6-6*T
        tested.append(dict(r,slack=slack,compatible=slack>=0))
    violations=[r for r in tested if not r["compatible"]]
    report=dict(passed=not violations,tested=len(tested),distinct_orders=len({r["n"] for r in tested}),
        conjecture="For every even n>=4,6T<=n(2n-5)+6 for arbitrary real line-arrangement multiplicities",
        status="No proof, only bounded sanity testing; no general upper theorem follows",
        tight_cases=[r for r in tested if r["slack"]<6],violations=violations,cases=tested)
    (OUT/"even-plus-one-sanity.json").write_text(json.dumps(report,indent=2)+"\n")
    print(json.dumps({k:report[k] for k in ["passed","tested","distinct_orders","violations","status"]}))
