"""Report the exact even triple-only correction, not just a Boolean failure."""
from pathlib import Path
from collections import Counter
import json
ROOT=Path(__file__).resolve().parents[3];BASE=ROOT/'research/openmath-seven-hour-2026-10-05/corpus'

if __name__=='__main__':
    raw=json.loads((BASE/'triple-curvature-sanity.json').read_text());rows=[]
    for r in raw['records']:
        if r['n']%2 or r['n']<4:continue
        assert not r['H'] and all(int(m)==3 for m in r['multiplicities'])
        rows.append(dict(r,n_mod6=r['n']%6,maximum_multiplicity=3 if r['q'] else 2,gap=r['n']-2*r['U']-r['D1']-r['Rc']))
    maxima={r:max(x['gap'] for x in rows if x['n_mod6']==r) for r in sorted({x['n_mod6'] for x in rows})}
    fp=json.loads((BASE/'fp-deletion-curvature/report.json').read_text())
    result=dict(scope='Exact finite nonparallel, multiplicity-at-most-three even arrangements; no corrected global theorem inferred',tested_even=len(rows),maximum_gap=max(r['gap'] for r in rows),maxima_by_residue6=maxima,all_positive_gap_records=[r for r in rows if r['gap']>0],fp_deleted_worst=fp['worst_even_first_token'],fp_subsets_tested=fp['tests'])
    (BASE/'first-token-maximum.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(dict(tested_even=len(rows),maximum_gap=result['maximum_gap'],maxima_by_residue6=maxima,fp_deleted_worst=fp['worst_even_first_token'])))
