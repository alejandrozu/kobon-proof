"""Audit every 40-line deletion of the saved optimal 41-line witness.

The projective census is exact. The four potentially useful chart changes
are checked by the rational-linear SMT solver, not by numerical sampling.
This is reproducible solver evidence, not a Lean-verified impossibility.
"""
from chart_retention import *
import hashlib


def audit():
    source=ROOT/'research/finite-table/classical-041.json'
    destination=Path(__file__).parent
    lines=read_lines(source);records=[]
    for removed in range(len(lines)):
        candidate=lines[:removed]+lines[removed+1:]
        ar=arrangement(candidate);total=len(projective_faces(ar)[1]);count=len(ar['triangles'])
        row=dict(removed=removed,affine=count,projective=total)
        if total>494:
            seed=destination/f'delete41-line{removed}.json'
            out=destination/f'smt-delete41-line{removed}-audit.json'
            save_result(seed,candidate,count,str(source.relative_to(ROOT)),
                        'Delete one line',dict(removed=removed))
            result=run(seed,out,495,180000,True)
            row.update(result=result['result'],report=str(Path(str(out)+'.report.json').relative_to(ROOT)))
        else:row['result']='impossible by exact projective face count'
        records.append(row)
    report=dict(source=str(source.relative_to(ROOT)),source_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),
                target_order=40,target_triangles=495,all_deletions_tested=len(records),records=records,
                scope='Exact projective census plus QF_LRA solver evidence; not a Lean theorem.')
    (destination/'deletion41-chart-audit.json').write_text(json.dumps(report,indent=2))
    print(json.dumps(dict(event='deletion_chart_audit_done',tested=len(records),
                         statuses={str(s):sum(r['result']==s for r in records)
                                   for s in sorted(set(r['result'] for r in records))})),flush=True)


if __name__=='__main__':audit()
