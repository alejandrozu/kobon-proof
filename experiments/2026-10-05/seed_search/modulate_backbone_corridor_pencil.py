"""Bounded exact point screen of independent perturbations in a BBL pencil.

The original eight lines, including its two exact triple points, remain fixed.
Only six new pencil directions vary; all counts are rational arrangement
replays. This does not prove that any modulation iterates.
"""
from pathlib import Path
from fractions import Fraction as F
import json,math,sys,itertools as it,time,random,argparse
ROOT=Path(__file__).resolve().parents[3]
sys.path.insert(0,str(ROOT/'research/kobon-hybrid'))
sys.path.insert(0,str(ROOT/'experiments/2026-10-05/corpus'))
sys.path.insert(0,str(Path(__file__).resolve().parent))
from exact_geometry import arrangement,primitive
from check_global_token_hypotheses import ledger
from test_backbone_corridor_doubling import profile

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--seconds',type=int,default=180);ap.add_argument('--seed',type=int,default=621);args=ap.parse_args()
    start=time.time();rng=random.Random(args.seed);base=ROOT/'research/openmath-seven-hour-2026-10-05/seed_search/backbone-corridor-bbl';out=base/f'modulated-seed{args.seed}';out.mkdir(parents=True,exist_ok=True)
    seeds=[(p,json.loads(p.read_text())) for p in sorted(base.glob('seed-axis*.json'))];roots=[F(math.tan(math.pi*k/12)).limit_denominator(10**15) for k in [-5,-3,-1,1,3,5]]
    best=53;tested=0;wins=[];hist={};bestback=0
    while time.time()-start<args.seconds:
        source,raw=rng.choice(seeds);old=[tuple(map(F,l)) for l in raw['lines_frac']];ci=raw['corridor_index'];eps=F(raw['epsilon']);delta=F(1,10**rng.choice([3,5,7]));kappa=delta*eps**rng.choice([1,2,3])
        mode=rng.choice(['individual','even','odd','paired','rational'])
        if mode=='individual':u=[F(rng.randint(-20,40),10) for _ in roots]
        elif mode=='even':v=[F(rng.randint(-20,40),10) for _ in range(3)];u=v+list(reversed(v))
        elif mode=='odd':v=[F(rng.randint(-20,40),10) for _ in range(3)];u=v+[-z for z in reversed(v)]
        elif mode=='paired':u=[F(1)+F(rng.randint(-20,20),100) for _ in roots]
        else:u=[F(rng.randint(-100,200),100) for _ in roots]
        added=[(m,F(-1),m*t) for t,v in zip(roots,u) for m in [kappa*(2*t/(1+t*t)+delta*v/t)]]
        lines=list(map(primitive,old+added));ar=arrangement(lines);T=len(ar['triangles']);tested+=1;hist[T]=hist.get(T,0)+1
        if T<best:continue
        p=profile(lines,ci);back=p['backbone_T'];bestback=max(bestback,back)
        if T>best:
            best=T;print(json.dumps(dict(event='best',trial=tested,mode=mode,**p)),flush=True)
        if T>=54:
            dst=out/f'trial{tested}-T{T}-back{back}.json';rec=dict(source=str(source.relative_to(ROOT)),trial=tested,mode=mode,delta=str(delta),kappa=str(kappa),perturbations=list(map(str,u)),corridor_index=ci,**p,lines_frac=[[str(v) for v in l] for l in lines],status='Exact rational independently modulated point; no uniform or scalable claim')
            dst.write_text(json.dumps(rec,indent=2)+'\n');wins.append(str(dst.relative_to(ROOT)));print(json.dumps(dict(event='win',trial=tested,path=str(dst.relative_to(ROOT)),**p)),flush=True)
            if T>=54 and back>=47:break
    report=dict(best=best,best_backbone=bestback,tested=tested,wins=wins,histogram=hist,seconds=time.time()-start,seed=args.seed,scope='Bounded point modulation, independent exact rational recounts; an infinite-family theorem remains open')
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report),flush=True)
