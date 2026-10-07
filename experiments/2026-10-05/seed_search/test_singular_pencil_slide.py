"""Finite diagnostic of a singular-grid pencil and local core-root transfer.

New half-grid lines use the existing BBL slope factor. A plain interleaving
doubles the separation of the singular roots. A local transfer of one duplicate
old line to a neighboring new root restores their adjacency. No recurrence is
assumed; every displayed count is independently exact rational geometry.
"""
from pathlib import Path
from fractions import Fraction as F
import json,math,sys,itertools as it,time
ROOT=Path(__file__).resolve().parents[3];sys.path.insert(0,str(ROOT/'research/kobon-hybrid'));sys.path.insert(0,str(ROOT/'experiments/2026-10-05/corpus'))
from exact_geometry import arrangement,primitive
from check_global_token_hypotheses import ledger

if __name__=='__main__':
    start=time.time();base=ROOT/'research/openmath-seven-hour-2026-10-05/seed_search/singular-corridor-grid';source=base/'n008-sourceparpalak-utkin-current-certificate-008-proposal.json';raw=json.loads(source.read_text());old=[tuple(map(F,l)) for l in raw['lines_frac']];q=6
    positive=min(c for a,b,c in old[1:] if c>0);extra=[i for i,(a,b,c) in enumerate(old) if c==positive];assert len(extra)==2
    roots=[F(float(math.tan(math.pi*k/(2*q)))).limit_denominator(10**15) for k in range(-q+1,q,2)];first=min(x for x in roots if x>0);out=ROOT/'research/openmath-seven-hour-2026-10-05/seed_search/singular-pencil-slide';out.mkdir(parents=True,exist_ok=True);records=[];best=0;wins=[]
    for delta,kappa in it.product([F(s,10**r) for r in [2,3,4,5,6] for s in [1,-1]],[F(s,10**r) for r in [2,3,4,5,6,8] for s in [1,-1]]):
        added=[]
        for t in roots:
            m=kappa*(2*t/(1+t*t)+delta/t);added.append((m,F(-1),m*t))
        for moved,scale in [(None,F(1))]+[(i,s) for i in extra for s in [F(1),kappa,1/kappa]]:
            kept=old.copy()
            if moved is not None:
                a,b,c=kept[moved];kept[moved]=(a*scale,b,first*a*scale)
            lines=list(map(primitive,kept+added));r=ledger(lines)
            if r is None:continue
            axis_count=sum(0 in t for t in arrangement(lines)['triangles']);item=dict(delta=str(delta),kappa=str(kappa),moved=moved,slope_scale=str(scale),axis_triangles=axis_count,**r);records.append(item)
            if r['T']>best:
                best=r['T'];print(json.dumps(dict(event='best',**item)),flush=True)
            if r['T']>=54:
                p=out/f'T{r["T"]}-move{moved}-scale{str(scale).replace("/","_")}-d{delta.numerator}_{delta.denominator}-k{kappa.numerator}_{kappa.denominator}.json';p.write_text(json.dumps(dict(item,lines_frac=[[str(v) for v in l] for l in lines],source=str(source.relative_to(ROOT)),status='Exact rational half-grid prototype only; true tangent intervals and an iteration theorem not yet proved'),indent=2)+'\n');wins.append(str(p.relative_to(ROOT)))
    (out/'report.json').write_text(json.dumps(dict(best=best,wins=wins,records=records,seconds=time.time()-start,scope='Finite singular-pencil/core-transfer screen, no all-order geometric claim'),indent=2)+'\n');print(json.dumps(dict(best=best,wins=len(wins),tested=len(records),seconds=time.time()-start)),flush=True)
