"""Recheck the ordinary interval argument without modifying frozen evidence."""
from pathlib import Path
import json,sys
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'research/kobon-hybrid'))
from verify_seed import verify_seed

if __name__=='__main__':
    dest=ROOT/'work/seed-interval-check';dest.mkdir(parents=True,exist_ok=True)
    report=verify_seed(dest)
    for name in ('seed-11-rational.json','seed-combinatorics.json','seed-verification.json'):
        assert json.loads((dest/name).read_text())==json.loads((ROOT/'research/kobon-hybrid'/name).read_text())
    (ROOT/'verification/seed-interval-summary.json').write_text(json.dumps(report,indent=2)+'\n')
    print('PASS: regenerated seed and interval data match the preserved evidence.')
