"""Exact bounded screen of D1<=2q in the actual triple-only class."""
from pathlib import Path
import json,re,sys,time,random
ROOT=Path(__file__).resolve().parents[3]
sys.path.insert(0,str(Path(__file__).resolve().parent))
from check_global_token_hypotheses import ledger

if __name__=="__main__":
    start=time.time();tested=[];violations=[];skipped=0
    def test(lines,source):
        global skipped
        r=ledger(lines)
        if r is None or any(int(m)>3 for m in r["multiplicities"]):skipped+=1;return False
        r.update(source=source,ordinary_slack=2*r["q"]-r["D1"]);tested.append(r)
        if r["ordinary_slack"]<0:violations.append(dict(r,lines_frac=lines));return True
        return False
    base=ROOT/"work/openmath-rohith/kobon-triangles"
    for row in (base/"RESULTS.md").read_text().splitlines():
        m=re.match(r"\| (\d+) \| (\d+) \|",row)
        if not m:continue
        path=base/f"submissions/n{m.group(1)}/solution.json"
        if not path.exists():continue
        raw=json.loads(path.read_text())
        if test([(a,b,-c) for a,b,c in raw["lines"]],str(path.relative_to(ROOT))):break
    if not violations:
        catalog=json.loads((ROOT/"manuscripts/2026-10-03/long/generated/certificate-catalog.json").read_text())
        for r in catalog:
            if r["n"]>70:continue
            source=r["sources"][0];raw=json.loads((ROOT/source).read_text())
            if test(raw["lines_frac"],source):break
    output=dict(passed=not violations,scope="D1<=2q, pairwise nonparallel, multiplicity<=3; no general theorem proved by this script",tested=tested,violations=violations,skipped=skipped,seconds=time.time()-start)
    out=ROOT/"research/openmath-seven-hour-2026-10-05/corpus/triple-ordinary-shared-sanity.json"
    out.write_text(json.dumps(output,indent=2)+"\n")
    print(json.dumps(dict(cases=len(tested),violations=violations,skipped=skipped,seconds=output["seconds"])),flush=True)
