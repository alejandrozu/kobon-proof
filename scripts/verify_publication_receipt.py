"""Verify a clean Lean CI receipt against the exact current source closure.

The original workflow's overall conclusion is retained: a successful Lean
step is not relabelled as a successful complete workflow. Remaining exact
replays and document checks run separately in the publication workflow.
"""
from pathlib import Path
import argparse,hashlib,json,re
ROOT=Path(__file__).resolve().parents[1]
def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--artifact',type=Path,required=True)
    p.add_argument('--metadata',type=Path,required=True)
    p.add_argument('--math-commit',required=True)
    p.add_argument('--run-id',required=True,type=int)
    p.add_argument('--out',type=Path,required=True);a=p.parse_args()
    meta=json.loads(a.metadata.read_text(encoding='utf-8-sig'))
    head=meta.get('headSha',meta.get('head_sha'));assert head==a.math_commit
    steps=[s for job in meta['jobs'] for s in job.get('steps',[])]
    required=['Build all results and audit axioms','Check all finite coordinates independently','Recheck the separate rational interval argument']
    for name in required:assert any(s['name']==name and s['conclusion']=='success' for s in steps),name
    summary=json.loads((a.artifact/'lean-summary.json').read_text())
    assert summary['complete'] and all(x['passed'] for x in summary['results'])
    assert not summary.get('source_changes_during_build',[])
    active=[ROOT/'Kobon.lean',*sorted((ROOT/'Kobon').rglob('*.lean'))]
    actual={x.relative_to(ROOT).as_posix():hashlib.sha256(x.read_bytes()).hexdigest() for x in active}
    assert actual==summary['source_sha256'],'Current mathematical sources differ from the clean CI receipt.'
    coords=json.loads((a.artifact/'coordinate-summary.json').read_text())
    assert len(coords['results'])==138 and all(x['passed'] for x in coords['results'])
    log=(a.artifact/'build-logs/Kobon.Audit.log').read_text(encoding='utf-8')
    assert 'Unapproved axiom' not in log and 'sorryAx' not in log
    total=int(re.search(r'AUDIT_TOTAL (\d+)',log)[1]);assert total==9058
    a.out.parent.mkdir(parents=True,exist_ok=True)
    report=dict(passed=True,math_commit=a.math_commit,clean_lean_run=a.run_id,
        clean_lean_run_url=f'https://github.com/alejandrozu/kobon-proof/actions/runs/{a.run_id}',
        original_workflow_conclusion=meta['conclusion'],verified_successful_steps=required,
        active_sources=len(actual),requested_build_targets=len(summary['results']),audited_declarations=total,
        clean_summary_sha256=hashlib.sha256((a.artifact/'lean-summary.json').read_bytes()).hexdigest(),
        scope='Exact current source hashes equal a fresh successful Lean build and axiom audit; coordinate and interval steps also passed. Overall original workflow status is preserved. Remaining publication checks run independently.')
    a.out.write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8')
    print(f'PASS: clean proof receipt, {len(actual)} exact source hashes, {total} audited declarations.')
if __name__=='__main__':main()
