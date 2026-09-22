"""Projective triangle mutations followed by exact concurrent-face boundaries.

Unlike a simple-cell hill climb, score the singular boundary itself. Search
states are combinatorial until a fixed-normal LP and exact rational sign check
realize all contractions. No bound is claimed from failed finite searches.
"""
import argparse,hashlib,importlib.util,itertools,json,random,sys,time
from pathlib import Path
ROOT=Path(__file__).resolve().parents[3]
sys.path.insert(0,str(ROOT/'experiments/2026-09-21/construction-search'))
sys.path.insert(0,str(Path(__file__).parent))
from beam_mutation import ProjectiveChamber,apply_flip,read_lines
spec=importlib.util.spec_from_file_location('general_bounds_collapse_search',Path(__file__).with_name('collapse_search.py'))
local_collapse=importlib.util.module_from_spec(spec);spec.loader.exec_module(local_collapse)
Census,realize,OUT=local_collapse.Census,local_collapse.realize,local_collapse.OUT

def boundary(ch,zeros):
    touched=set(p for q in zeros for p in ch.ts[q]);saved={p:(ch.pos[p],ch.neg[p])for p in touched}
    affected=set(r for q in zeros for r in ch.affected[q]);old=sum(ch.empty[r]for r in affected)
    for q in zeros:
        i,j,k=ch.triples[q]
        for p,r in zip(ch.ts[q],(k,j,i)):
            ch.pos[p]&=~(1<<r);ch.neg[p]&=~(1<<r)
    new=sum(ch.is_empty(r)for r in affected if r not in zeros)
    for p,(P,N)in saved.items():ch.pos[p]=P;ch.neg[p]=N
    return ch.score+new-old

def run(path,seconds,width,depth,drop,seed):
    OUT.mkdir(exist_ok=True);rng=random.Random(seed);start=last=time.monotonic()
    lines=read_lines(ROOT/path);ch=ProjectiveChamber(lines);C=Census(lines)
    initial=ch.score;best=initial;cbest=initial;rounds=nodes=edges=lp=0;tested=set();events=[];all_hist={}
    reportpath=OUT/f'beam-{ch.n:03d}.json'
    while time.monotonic()-start<seconds:
        rounds+=1;rows=[((),0,ch.score,ch.pscore)];seen={0}
        for level in range(depth+1):
            children=[]
            for flips,mask,score,pscore in rows:
                for q in flips:apply_flip(ch,q)
                assert(ch.score,ch.pscore)==(score,pscore);nodes+=1
                eligible=[];targets=[]
                for q,empty in enumerate(ch.empty):
                    if not empty:continue
                    bscore=boundary(ch,{q});cbest=max(cbest,bscore)
                    if bscore>best:targets.append((bscore,(q,)))
                    if bscore>=initial-1:eligible.append(q)
                for a,b in itertools.combinations(eligible,2):
                    if len(set(ch.triples[a])&set(ch.triples[b]))!=1:continue
                    bscore=boundary(ch,{a,b});cbest=max(cbest,bscore)
                    if bscore>best:targets.append((bscore,tuple(sorted((a,b)))))
                targets.sort(reverse=True)
                for sc,qs in targets:
                    key=(mask,qs)
                    if key in tested:continue
                    tested.add(key);lp+=1
                    olddet=C.det;C.det={t:s for t,s in zip(ch.triples,ch.signs)}
                    try:data,info=realize(C,{ch.triples[q]for q in qs},5)
                    finally:C.det=olddet
                    event=dict(round=rounds,level=level,source_score=score,predicted=sc,
                        flips=[ch.triples[q]for q in flips],zeros=[ch.triples[q]for q in qs],
                        lp=info,realized=data is not None,seconds=time.monotonic()-start)
                    events.append(event)
                    if data:
                        assert data['triangle_count']==sc;best=sc
                        data.update(source=path,construction='Projective triangle mutations followed by exact concurrent-face contractions',event=event)
                        out=OUT/f'beam-n{ch.n:03d}-T{sc:05d}.json';out.write_text(json.dumps(data,indent=2)+'\n')
                        print('EXACT IMPROVEMENT',str(out),flush=True)
                    if time.monotonic()-start>=seconds:break
                if level<depth:
                    for q,empty in enumerate(ch.pempty):
                        if not empty:continue
                        nxt=mask^(1<<q)
                        if nxt in seen:continue
                        gain,pgain=ch.gains(q);edges+=1;sc=score+gain;psc=pscore+pgain
                        if sc<initial-drop:continue
                        seen.add(nxt)
                        # Preserve score while allowing enough lower-score chambers
                        # to expose quadrilateral neighbors at a contraction.
                        rank=sc+.05*psc+1.0*rng.expovariate(1)
                        children.append((rank,flips+(q,),nxt,sc,psc))
                for q in reversed(flips):apply_flip(ch,q)
                if time.monotonic()-last>30:
                    print(json.dumps(dict(round=rounds,level=level,nodes=nodes,edges=edges,lp=lp,best=best,
                        boundary_combinatorial_best=cbest,seconds=time.monotonic()-start)),flush=True);last=time.monotonic()
                if time.monotonic()-start>=seconds:break
            if not children or time.monotonic()-start>=seconds:break
            children.sort(reverse=True);rows=[(p,m,s,ps)for _,p,m,s,ps in children[:width]]
        assert ch.score==initial
        report=dict(source=path,n=ch.n,initial=initial,best=best,combinatorial_boundary_best=cbest,
            rounds=rounds,nodes=nodes,edges=edges,lp_attempts=lp,width=width,depth=depth,drop=drop,seed=seed,
            seconds=time.monotonic()-start,events=events,limitations='Heuristic topology search; floating LP negatives are not infeasibility certificates.')
        reportpath.write_text(json.dumps(report,indent=2)+'\n')
    print('DONE',json.dumps({k:v for k,v in report.items()if k!='events'}),flush=True)

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--source',default='research/finite-table/classical-044.json')
    p.add_argument('--seconds',type=float,default=1800);p.add_argument('--width',type=int,default=16)
    p.add_argument('--depth',type=int,default=16);p.add_argument('--drop',type=int,default=4);p.add_argument('--seed',type=int,default=2026092206)
    a=p.parse_args();run(a.source,a.seconds,a.width,a.depth,a.drop,a.seed)
