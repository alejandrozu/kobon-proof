"""Exact rational diagnostic of BBL doubling with an extra interior corridor.

This retains a simple saturated BBL backbone, rather than doubling about the
concurrent corridor. Point data are rational tangent approximations; an exact
finite count alone is not a uniform or infinite-family certificate.
"""
from pathlib import Path
from fractions import Fraction as F
import json, math, sys, itertools as it, time
ROOT=Path(__file__).resolve().parents[3]
sys.path.insert(0,str(ROOT/'research/kobon-hybrid'))
sys.path.insert(0,str(ROOT/'experiments/2026-10-05/corpus'))
from exact_geometry import arrangement, primitive
from check_global_token_hypotheses import ledger

def pencil(q,delta,kappa):
    roots=[F(math.tan(math.pi*k/(2*q))).limit_denominator(10**15) for k in range(-q+1,q,2)]
    return [(m,F(-1),m*t) for t in roots for m in [kappa*(2*t/(1+t*t)+delta/t)]]

def profile(lines,corridor):
    ar=arrangement(lines);back=arrangement([l for i,l in enumerate(lines) if i!=corridor])
    old_n=len(lines)-len(lines)//2+1
    backbone_T=len(back['triangles']);corridor_triangles=sum(corridor in t for t in ar['triangles'])
    return dict(ledger=ledger(lines),backbone_T=backbone_T,corridor_triangles=corridor_triangles,
        recovered_on_deletion=backbone_T-(len(ar['triangles'])-corridor_triangles),
        axis_triangles=sum(0 in t for t in ar['triangles']),
        backbone_axis_triangles=sum(0 in t for t in back['triangles']))

if __name__=='__main__':
    start=time.time();base=ROOT/'research/openmath-seven-hour-2026-10-05/seed_search/backbone-corridor-bbl'
    out=base/'doubling';out.mkdir(parents=True,exist_ok=True);records=[];wins=[];best=0
    for source in sorted(base.glob('seed-axis*.json')):
        raw=json.loads(source.read_text());old=[tuple(map(F,l)) for l in raw['lines_frac']];eps=F(raw['epsilon']);corridor=raw['corridor_index']
        for delta in [F(1,10**r) for r in [3,5,7,9]]:
            for scale in [eps,eps**2,eps**3]:
                kappa=delta*scale;lines=list(map(primitive,old+pencil(6,delta,kappa)));p=profile(lines,corridor)
                rec=dict(source=str(source.relative_to(ROOT)),delta=str(delta),kappa=str(kappa),**p);records.append(rec)
                if p['ledger'] and p['ledger']['T']>best:
                    best=p['ledger']['T'];print(json.dumps(dict(event='best',**rec)),flush=True)
                if p['ledger'] and p['ledger']['T']>=54:
                    name=f'{source.stem}-d{delta.denominator}-k{kappa.denominator}.json';dst=out/name
                    dst.write_text(json.dumps(dict(rec,corridor_index=corridor,lines_frac=[[str(v) for v in l] for l in lines],status='Exact rational coupled doubling point; true-tangent and scalable proof pending'),indent=2)+'\n');wins.append(str(dst.relative_to(ROOT)))
    report=dict(best=best,records=records,wins=wins,seconds=time.time()-start,scope='48 exact rational controls of backbone-axis doubling, no uniform/infinite claim')
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(dict(best=best,wins=len(wins),seconds=report['seconds'])),flush=True)
