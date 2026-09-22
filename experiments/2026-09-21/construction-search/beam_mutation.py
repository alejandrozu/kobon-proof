"""Bounded beam search across several projective triangle mutations.

Combinatorial paths need not be realizable by straight lines. Only successful
LP realization followed by exact orientation and independent triangle checks
can produce a promoted candidate. Failed beam searches prove no upper bound.
"""
from projective_mutation import *
import hashlib


def apply_flip(ch,q):
    old=sum(ch.empty[r] for r in ch.affected[q])
    pold=sum(ch.pempty[r] for r in ch.affected[q])
    ch.toggle(q)
    for r in ch.affected[q]:
        ch.empty[r]=ch.is_empty(r)
        ch.pempty[r]=ch.is_projective_empty(r)
    ch.score+=sum(ch.empty[r] for r in ch.affected[q])-old
    ch.pscore+=sum(ch.pempty[r] for r in ch.affected[q])-pold


def realize_target(ch,mode):
    # Chamber.realize flips one designated bit, so reverse that bit just for
    # this call; its exact check then tests the entire desired target vector.
    ch.signs[0]*=-1
    try:return Chamber.realize(ch,0,mode)
    finally:ch.signs[0]*=-1


def beam(path,out,seconds=900,width=25,depth=12,drop=3,seed=20260925):
    rng=random.Random(seed);start=last=time.time()
    lines=read_lines(path);ch=ProjectiveChamber(lines)
    initial=ch.score;initialp=ch.pscore;best=initial;cbest=initial;pcbest=initialp
    rounds=nodes=edges=lp=0;events=[];tested=set();bestlines=lines
    print(json.dumps(dict(event='beam_start',n=ch.n,initial=initial,projective=initialp,
        width=width,depth=depth,drop=drop,seed=seed)),flush=True)
    while time.time()-start<seconds:
        rounds+=1;beamrows=[((),0,ch.score,ch.pscore)];seen={0}
        for level in range(1,depth+1):
            choices=[]
            for flips,mask,score,pscore in beamrows:
                for q in flips:apply_flip(ch,q)
                assert(ch.score,ch.pscore)==(score,pscore)
                nodes+=1
                for q,empty in enumerate(ch.pempty):
                    if not empty:continue
                    targetmask=mask^(1<<q)
                    if targetmask in seen:continue
                    gain,pgain=ch.gains(q);edges+=1
                    sc=score+gain;psc=pscore+pgain
                    if sc<initial-drop:continue
                    child=flips+(q,)
                    cbest=max(cbest,sc);pcbest=max(pcbest,psc)
                    if sc>best and targetmask not in tested:
                        tested.add(targetmask);apply_flip(ch,q)
                        record=dict(round=rounds,level=level,score=sc,projective=psc,
                            triangles=[ch.triples[t] for t in child],seconds=time.time()-start)
                        for mode in ('offset','normal'):
                            lp+=1;candidate,reason=realize_target(ch,mode)
                            if candidate is not None:
                                assert len(arrangement(candidate)['triangles'])==sc
                                best=sc;bestlines=candidate
                                record.update(realized=True,mode=mode,margin=reason)
                                save_result(out,candidate,best,str(path),
                                    'Multiple triangle mutations with exact-checked LP realization',record)
                                verify(out)
                                print(json.dumps(dict(event='beam_realized_record',**record)),flush=True)
                                break
                        else:record['realized']=False
                        events.append(record)
                        apply_flip(ch,q)
                    seen.add(targetmask)
                    # Score first, but ties explore different projective totals
                    # and mutation paths in each reproducibly seeded round.
                    rank=sc+.15*psc+.45*rng.expovariate(1)
                    choices.append((rank,child,targetmask,sc,psc))
                    if time.time()-start>=seconds:break
                for q in reversed(flips):apply_flip(ch,q)
                if time.time()-start>=seconds:break
            if not choices:break
            choices.sort(key=lambda x:x[0],reverse=True)
            beamrows=[(p,m,s,ps) for _,p,m,s,ps in choices[:width]]
            if time.time()-last>30:
                print(json.dumps(dict(event='beam_progress',round=rounds,level=level,
                    realized_best=best,combinatorial_best=cbest,projective_best=pcbest,
                    nodes=nodes,edges=edges,lp=lp,seconds=time.time()-start)),flush=True)
                last=time.time()
            if time.time()-start>=seconds:break
        # Keep the original geometry across rounds so all target masks use a
        # stable, audited origin and the LP constraints remain reproducible.
        assert ch.score==initial and ch.pscore==initialp
        Path(str(out)+'.progress.json').write_text(json.dumps(dict(events=events,
            rounds=rounds,nodes=nodes,edges=edges,lp=lp,realized_best=best,
            combinatorial_best=cbest,projective_best=pcbest),indent=2))
    report=dict(source=str(path),source_sha256=hashlib.sha256(Path(path).read_bytes()).hexdigest(),
        n=ch.n,initial=initial,initial_projective=initialp,realized_best=best,
        combinatorial_best=cbest,combinatorial_projective_best=pcbest,
        rounds=rounds,nodes=nodes,edges=edges,lp_attempts=lp,events=events,
        width=width,depth=depth,drop=drop,seed=seed,seconds=time.time()-start,
        limitations='Bounded search; combinatorial states are not claimed realizable. No upper-bound conclusion.')
    Path(str(out)+'.report.json').write_text(json.dumps(report,indent=2))
    print(json.dumps(dict(event='beam_done',**{k:v for k,v in report.items() if k!='events'})),flush=True)


if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('path');p.add_argument('out')
    p.add_argument('--seconds',type=float,default=900);p.add_argument('--width',type=int,default=25)
    p.add_argument('--depth',type=int,default=12);p.add_argument('--drop',type=int,default=3)
    p.add_argument('--seed',type=int,default=20260925)
    a=p.parse_args();beam(a.path,a.out,a.seconds,a.width,a.depth,a.drop,a.seed)
