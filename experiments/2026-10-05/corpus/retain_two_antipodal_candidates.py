"""Retain exact multi-star cases encountered by the bounded recipient screen."""
from pathlib import Path
from itertools import combinations
import ast,json,sys
ROOT=Path(__file__).resolve().parents[3];BASE=ROOT/'research/openmath-seven-hour-2026-10-05/corpus'
sys.path.insert(0,str(ROOT/'research/kobon-hybrid'));sys.path.insert(0,str(Path(__file__).resolve().parent))
from exact_geometry import primitive
from stress_two_antipodal_recipients import profiles,assess
from check_global_token_hypotheses import ledger

def main():
    src=json.loads((BASE/'two-antipodal-recipient-stress.json').read_text());cases=[]
    for r in src['records']:
        if r['A0']<2 or 'added_line' not in r:continue
        parts=r['source'].split(' plus ')
        lines=[primitive(l) for l in json.loads((BASE/parts[0]).read_text())['lines_frac']]
        lines.extend(ast.literal_eval(s) for s in parts[1:])
        lines.append(primitive(r['added_line']))
        pp=profiles(lines);A,R,m=assess(pp)
        assert len(A)==r['A0'] and len(lines)==r['n'] and m==r['max_N13_A0']
        common=[dict(centers=[p,q],shared_neighbors=sorted(set(pp[p]['neighbors'])&set(pp[q]['neighbors']))) for p,q in combinations(sorted(A),2)]
        assert all(len(c['shared_neighbors'])<4 for c in common)
        cases.append(dict(source=r['source'],lines_frac=[[str(x) for x in l] for l in lines],ledger=ledger(lines),antipodal_centers=sorted(A),common_neighbor_profiles=common,one_cap_recipients=R,profiles=list(pp.values())))
    out=dict(cases=cases,count=len(cases),maximum_common_neighbor_count=max((len(c['shared_neighbors']) for r in cases for c in r['common_neighbor_profiles']),default=0),scope='Exact retained finite cases, not a new lower-bound record or an all-order exclusion.')
    (BASE/'two-antipodal-star-candidates.json').write_text(json.dumps(out,indent=2)+'\n')
    print('Retained',len(cases),'exact two-star arrangements; maximum common neighbors',out['maximum_common_neighbor_count'])
if __name__=='__main__':main()
