"""Reoptimize one line at a time; exact-check all accepted changes.

For each proposed rational normal, evaluate all vertex offsets and intervening
intervals. Scores are numerical proposals; the saved coordinate certificates
use rational arithmetic and exact counting. Optional equal-score moves explore
different arrangements; they do not establish a global maximum.
"""
from hybrid_search import *
import random


def offset_proposals(sc,a,b):
    # Numerically order offsets; rationally reconstruct only selected proposals.
    scale=max(abs(a),abs(b))
    af,bf=float(F(a,scale)),float(F(b,scale))
    xy=sc.xyz[:sc.finite,:2]/sc.xyz[:sc.finite,2,None]
    h=af*xy[:,0]+bf*xy[:,1]
    order=np.argsort(h);values=h[order]
    cs=np.empty(2*len(values)+1)
    cs[1:-1:2]=values
    cs[2:-1:2]=(values[:-1]+values[1:])/2
    cs[0]=values[0]-1-abs(values[0]);cs[-1]=values[-1]+1+abs(values[-1])
    hs=np.column_stack((np.full(len(cs),af),np.full(len(cs),bf),-cs))
    return hs,order


def exact_offset(sc,a,b,order,j):
    def val(k):
        x,y,z=sc.coords[int(order[k])]
        return F(a*x+b*y,z)
    if j==0:c=val(0)-max(abs(a),abs(b))-abs(val(0))
    elif j==2*len(order):c=val(-1)+max(abs(a),abs(b))+abs(val(-1))
    elif j%2:c=val(j//2)
    else:c=(val(j//2-1)+val(j//2))/2
    return primitive((a,b,c))


def run(path,out,seconds=180,rounds=10,seed=20260920,plateau=False):
    rng=random.Random(seed)
    lines=read_lines(path);initial=len(arrangement(lines)['triangles']);score=initial
    best=score;bestlines=lines.copy();start=time.time();last=start;accepted=[];proposals=0
    tested=0;incorrect=0
    seen={tuple(lines)}
    rotations=[F(0),F(1,1000),F(-1,1000),F(1,100),F(-1,100),F(1,10),F(-1,10),F(1,2),F(-1,2)]
    print(json.dumps(dict(event='local_start',n=len(lines),score=score,seconds=seconds,plateau=plateau)),flush=True)
    for sweep in range(rounds):
        changed=False;indices=list(range(len(lines)));rng.shuffle(indices)
        for r in indices:
            if time.time()-start>seconds:break
            old=lines[r];rest=[l for j,l in enumerate(lines) if j!=r];sc=InsertionScore(rest)
            options=[]
            for rot in rotations:
                a,b=old[0]+rot*old[1],old[1]-rot*old[0]
                d=math.lcm(a.denominator if isinstance(a,F) else 1,b.denominator if isinstance(b,F) else 1)
                a,b=int(a*d),int(b*d)
                hs,order=offset_proposals(sc,a,b)
                scores=np.concatenate([sc.scores(hs[k:k+128]) for k in range(0,len(hs),128)])
                proposals+=len(scores)
                ids=np.flatnonzero(scores>score if not plateau else scores>=score)
                for j in ids:
                    options.append((int(scores[j]),rng.random(),a,b,order,int(j)))
            options.sort(key=lambda t:t[:2],reverse=True)
            for approximate,_,a,b,order,j in options:
                if approximate<score or approximate==score and not plateau:break
                l=exact_offset(sc,a,b,order,j)
                if l==old or l in rest:continue
                candidate=lines.copy();candidate[r]=l
                if tuple(candidate) in seen:continue
                seen.add(tuple(candidate));tested+=1
                exact=sc.exact_sign_score(l)
                if exact!=approximate:incorrect+=1
                if exact<score or exact==score and not plateau:continue
                # Keep the accepted sequence within the nonparallel problem.
                if any(l[0]*m[1]==l[1]*m[0] for m in rest):continue
                verified=len(arrangement(candidate)['triangles'])
                assert exact==verified,(exact,verified)
                lines=candidate;score=exact;changed=True
                event=dict(sweep=sweep,line=r,count=score,seconds=time.time()-start)
                accepted.append(event)
                if score>best:
                    best=score;bestlines=lines.copy()
                    save_result(out,lines,best,str(path),'one-line replacement with rational normal and vertex offset',
                                dict(initial=initial,accepted=accepted,proposals=proposals))
                    print(json.dumps(dict(event='local_improvement',n=len(lines),**event)),flush=True)
                break
            if time.time()-last>20:
                print(json.dumps(dict(event='local_progress',n=len(lines),best=best,current=score,sweep=sweep,
                                      accepted=len(accepted),proposals=proposals,seconds=time.time()-start)),flush=True);last=time.time()
        if not changed or time.time()-start>seconds:break
    report=dict(n=len(lines),source=str(path),initial=initial,best=best,accepted=len(accepted),
                proposals=proposals,exact_checked=tested,incorrect_float_scores=incorrect,seconds=time.time()-start,
                seed=seed,plateau=plateau,scope='Bounded heuristic search, not an optimality or priority proof')
    if not Path(out).exists():save_result(out,bestlines,best,str(path),'unchanged starting certificate',report)
    Path(str(out)+'.search.json').write_text(json.dumps(report,indent=2))
    print(json.dumps(dict(event='local_done',**report)),flush=True)


if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('path');p.add_argument('out')
    p.add_argument('--seconds',type=int,default=180);p.add_argument('--seed',type=int,default=20260920)
    p.add_argument('--rounds',type=int,default=10);p.add_argument('--plateau',action='store_true')
    a=p.parse_args();run(a.path,a.out,a.seconds,a.rounds,a.seed,a.plateau)
