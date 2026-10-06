"""Bounded multilevel exact diagnostic of the fixed-corridor BBL route.

True BBL backbone counts and full corridor counts are recorded independently.
Rational approximations are point experiments, not infinite certificates.
"""
from pathlib import Path
from fractions import Fraction as F
import sys,json,time,itertools as it
ROOT=Path(__file__).resolve().parents[3]
sys.path.insert(0,str(ROOT/'research/kobon-hybrid'))
sys.path.insert(0,str(ROOT/'experiments/2026-10-05/corpus'))
sys.path.insert(0,str(Path(__file__).resolve().parent))
from exact_geometry import arrangement,primitive
from test_backbone_corridor_doubling import pencil,profile

if __name__=='__main__':
    start=time.time();base=ROOT/'research/openmath-seven-hour-2026-10-05/seed_search/backbone-corridor-bbl';out=base/'iteration-points';out.mkdir(parents=True,exist_ok=True);reports=[]
    for source in sorted(base.glob('seed-axis*.json')):
        raw=json.loads(source.read_text());old=[tuple(map(F,l)) for l in raw['lines_frac']];ci=raw['corridor_index'];q=6;records=[]
        for step in range(1,5):
            delta=F(1,10**(4+step));kappa=F(1,10**(13+20*(step-1)));old=list(map(primitive,old+pencil(q,delta,kappa)));q*=2;p=profile(old,ci)
            rec=dict(step=step,q=q,delta=str(delta),kappa=str(kappa),odd_target=(q*q-3)//3,even_target=q*q//3+q//2,**p);records.append(rec)
            print(json.dumps(dict(source=source.name,**rec)),flush=True)
            if p['ledger'] and p['ledger']['T']>=rec['even_target']:
                dst=out/f'{source.stem}-q{q}-T{p["ledger"]["T"]}.json';dst.write_text(json.dumps(dict(rec,corridor_index=ci,source=str(source.relative_to(ROOT)),lines_frac=[[str(v) for v in l] for l in old],status_note='Exact rational multilevel point, not a true-tangent or iteration proof'),indent=2)+'\n')
        reports.append(dict(source=str(source.relative_to(ROOT)),records=records))
    (out/'report.json').write_text(json.dumps(dict(reports=reports,seconds=time.time()-start,scope='Four finite BBL-backbone iterations at four coupled seeds; no all-level assertion'),indent=2)+'\n')
