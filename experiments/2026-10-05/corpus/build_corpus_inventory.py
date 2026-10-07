"""Freeze a concise source inventory and compare supplied point counts to H.

Compilation receipts remain third-party evidence.  This script does not run
contestant code or turn judging recommendations into accepted theorems.
"""
from pathlib import Path
import hashlib,json,re

ROOT=Path(__file__).resolve().parents[3]
OUT=ROOT/"research/openmath-seven-hour-2026-10-05/corpus"
SOURCES={
 "archive":dict(repo="alejandrozu/openmath-2026-judging",commit="3dee18bdf290e70b2f9a6bd98b889d1b1b60b51c",dir="work/openmath-2026-judging",files=["README.md","OpenMath-Judging/contestants.json","OpenMath-Judging/review/problems/KOBON.txt","publication-review/2026-10-05/Sources/16_KOBON39.tex","publication-review/2026-10-05/Verification/htpeo-kobon471-fresh-build.json"]),
 "raj":dict(repo="srirangam-r/kobon_triangles",commit="eed14659a9b2f4ca12777da5d557f2b620b966f6",dir="work/openmath-raj",files=["README.md","NOVELTY.md","paper/kobon18.tex","proofs/additional/theorem_G_even_n.md","proofs/additional/special_column_identities.md","proofs/all8/ALL8_NOTE3.md","proofs/all8/ALL8_NOTE8.md"]),
 "rohith":dict(repo="Rohith18p/rsi-kobon-triangles",commit="f462d8e18aea2a458376c523c9b6c2980237071f",dir="work/openmath-rohith",files=["README.md","paper/kobon39.typ","kobon-triangles/RESULTS.md","kobon-triangles/src/doubling.py","kobon-triangles/src/basesearch.py","kobon-triangles/research/tools/edge_ledger.py","kobon-triangles/doubled/n19_107_bp19_d10.json","kobon-triangles/bases/n61_1190_base31.json"])}


def old_h(n,catalog):
    g=0 if n<3 else 1 if n==3 else n*(n-3)//3+1+n%2
    finite=max([r["triangles"] for r in catalog if r["n"]==n]+[0])
    recursive=0
    for t in range(n+1):
        q=10*2**t
        if q+1==n:recursive=max(recursive,(q*q-4)//3)
        if q+2==n:recursive=max(recursive,(q*q-4)//3+q//2)
        if q>n:break
    return max(g,finite,recursive)


if __name__=="__main__":
    OUT.mkdir(parents=True,exist_ok=True)
    for s in SOURCES.values():
        s["file_records"]=[dict(path=p,sha256=hashlib.sha256((ROOT/s["dir"]/p).read_bytes()).hexdigest(),url=f"https://github.com/{s['repo']}/blob/{s['commit']}/{p}") for p in s.pop("files")]
    contestants=json.loads((ROOT/"work/openmath-2026-judging/OpenMath-Judging/contestants.json").read_text())
    selected=[dict(group=r["group_id"],name=r["name"],repo=r.get("repo"),immutable_commit=r.get("immutable_commit"),claims=r.get("claims",r.get("contributions",[])),status=r.get("status")) for r in contestants if "kobon" in json.dumps(r).lower()]
    catalog=json.loads((ROOT/"manuscripts/2026-10-03/long/generated/certificate-catalog.json").read_text())
    table=(ROOT/"work/openmath-rohith/kobon-triangles/RESULTS.md").read_text()
    comparison=[]
    for line in table.splitlines():
        m=re.match(r"\| (\d+) \| (\d+) \|",line)
        if not m:continue
        n,t=map(int,m.groups());h=old_h(n,catalog)
        comparison.append(dict(n=n,contestant_point_count=t,previous_verified_repository_H=h,delta=t-h))
    output=dict(source_revisions=SOURCES,kobon_contact_records=len(selected),contact_inventory=selected,
                comparison_scope="Prior repository H at manuscript proof revision2d69a71; not a world-record priority judgment",
                point_comparison=comparison,strict_improvements=[r for r in comparison if r["delta"]>0],
                htpeo=dict(n=39,triangle_count=471,old_H=old_h(39,catalog),proof_status="55-module fresh standard-kernel receipt exists in public archive; not rerun in this corpus script"))
    (OUT/"source-inventory.json").write_text(json.dumps(output,indent=2)+"\n")
    print(json.dumps(dict(kobon_contact_records=len(selected),rohith_cases=len(comparison),strict_point_improvements=output["strict_improvements"],htpeo=output["htpeo"])))
