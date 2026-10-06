"""Exhaust slope chambers along individual coordinates inside the axis-cap cone.

Cap validity is a linear cone in reciprocal slopes when intercepts are fixed.
Only adjacent-root direction signs are retained; nonadjacent parallels and
other concurrence facets are chamber breakpoints, so this permits affine
chart changes and multi-facet jumps omitted by a fixed chirotope walk.
Floating scores are proposals, never certificates.
"""
from pathlib import Path
import sys,time,json,argparse,itertools as it,random,hashlib
from fractions import Fraction as F
ROOT=Path(__file__).resolve().parents[3]
sys.path.insert(0,str(ROOT/"experiments/2026-10-05/seed_search"))
from facet_walk61 import np,geometry,matrix


def main():
    p=argparse.ArgumentParser();p.add_argument("--minutes",type=float,default=10)
    p.add_argument("--passes",type=int,default=100);p.add_argument("--seed",type=int,default=309)
    p.add_argument("--q",type=int,choices=[30,60],default=60)
    p.add_argument("--temperature",type=float,default=0)
    p.add_argument("--max-intervals",type=int,default=0);args=p.parse_args()
    q=args.q
    if q==60:
        source=ROOT/"research/openmath-seven-hour-2026-10-05/constructions/contestant61-refitted-uniform-box.json"
        raw=json.loads(source.read_text());lo=list(map(F,raw["lo"]));hi=list(map(F,raw["hi"]));vals=[float((a+b)/2) for a,b in zip(lo,hi)]
        roots=np.array([vals[j]*s for j,s in raw["labels"][1:]])
        h=np.array([float(1/F(m)) for m in raw["slopes"][1:]])
    else:
        source=ROOT/"research/openmath-seven-hour-2026-10-05/constructions/contestant-limit-fits/n031-epsilon0.json"
        raw=json.loads(source.read_text());h=np.array(list(map(lambda x:float(F(x)),raw["reciprocal_slopes"])))
        tb=json.loads((ROOT/"research/openmath-seven-hour-2026-10-05/corpus/tangent60/bounds.json").read_text())
        vals=[float((F(tb[str(2*k)][0])+F(tb[str(2*k)][1]))/2) for k in range(1,q//2)]
        roots=np.array([-x for x in reversed(vals)]+[0.,0.]+vals)
    roots[q//2-1]=roots[q//2]=0.
    h=(h-h.min())/(h.max()-h.min())*2-1
    A,triples,pairs=matrix(roots);sg=np.sign(A@h)
    cap_rows=[row for t,row in triples.items() if t[1]==t[0]+1 or t[2]==t[1]+1]
    cap_rows += [pairs[i,i+1] for i in range(q-1)]
    C=A[cap_rows,:].multiply(sg[cap_rows,None]).tocsr();columns=C.tocsc();fullcolumns=A.tocsc()
    rng=random.Random(args.seed);start=time.time();deadline=start+args.minutes*60
    out=ROOT/f"research/openmath-seven-hour-2026-10-05/seed_search/coordinate{q+1}-seed{args.seed}";out.mkdir(parents=True,exist_ok=True)
    best=len(geometry(roots,h)["triangles"]);current=best
    records=[];evaluated=0;accepted=0
    for sweep in range(args.passes):
        order=list(range(q));rng.shuffle(order)
        for coordinate in order:
            if time.time()>deadline:break
            old=float(h[coordinate]);cv=C@h;minimum=float(cv.min());assert minimum>0,minimum
            safety=min(1e-9,minimum/1000)
            indices=columns.indices[columns.indptr[coordinate]:columns.indptr[coordinate+1]]
            cs=columns.data[columns.indptr[coordinate]:columns.indptr[coordinate+1]]
            nonzero=cs!=0;indices=indices[nonzero];cs=cs[nonzero]
            thresholds=(safety-(cv[indices]-cs*old))/cs
            lower=max(-2.,float(np.max(thresholds[cs>0])) if any(cs>0) else -2.)
            upper=min(2.,float(np.min(thresholds[cs<0])) if any(cs<0) else 2.)
            if upper-lower<1e-12:continue
            av=A@h;rr=fullcolumns.indices[fullcolumns.indptr[coordinate]:fullcolumns.indptr[coordinate+1]]
            dd=fullcolumns.data[fullcolumns.indptr[coordinate]:fullcolumns.indptr[coordinate+1]]
            nonzero=dd!=0;rr=rr[nonzero];dd=dd[nonzero]
            breaks=-(av[rr]-dd*old)/dd
            breaks=sorted([lower]+[float(x) for x in breaks if lower+1e-12<x<upper-1e-12]+[upper])
            unique=[breaks[0]]
            for x in breaks[1:]:
                if x-unique[-1]>1e-12:unique.append(x)
            candidates=[(a+b)/2 for a,b in zip(unique,unique[1:])]+[old]
            if args.max_intervals and len(candidates)>args.max_intervals:
                candidates=rng.sample(candidates[:-1],args.max_intervals-1)+[old]
            choices=[];counts={}
            for value in candidates:
                if time.time()>deadline:break
                hh=h.copy();hh[coordinate]=value
                if np.min(C@hh)<=0:continue
                if np.min(np.abs(A@hh))<1e-13:continue
                g=geometry(roots,hh);T=len(g["triangles"]);caps=sum(0 in t for t,v in g["triangles"])
                if caps!=q-1:raise RuntimeError((coordinate,T,caps,value,minimum))
                choices.append((T,value));counts[T]=counts.get(T,0)+1;evaluated+=1
            if not choices:continue
            high=max(T for T,v in choices)
            if args.temperature>0:
                eligible=[(T,v) for T,v in choices if T>=best-4]
                weights=[np.exp((T-high)/args.temperature) for T,v in eligible]
                selectedT,winner=rng.choices(eligible,weights=weights,k=1)[0]
            else:selectedT=high;winner=rng.choice([v for T,v in choices if T==high])
            # Neutral coordinate changes explore new cells; an occasional
            # one-triangle loss is only a search move, not a retained result.
            if selectedT>=current or args.temperature>0:
                h[coordinate]=winner;current=selectedT;accepted+=1
                h=(h-h.min())/(h.max()-h.min())*2-1
            record=dict(sweep=sweep,coordinate=coordinate,chambers=len(choices),best_coordinate=high,current=current,
                histogram={str(T):c for T,c in sorted(counts.items())},elapsed=time.time()-start)
            records.append(record)
            if current>best:
                best=current
                proposal=dict(n=q+1,triangle_screen=best,caps_screen=q-1,epsilon_screen="1e-10",
                    reciprocal_slopes=[str(F(float(x+2)).limit_denominator(10**12)) for x in h],
                    source=str(source.relative_to(ROOT)),source_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),
                    status="Floating cap-cone coordinate proposal; exact true-tangent interval verification required")
                path=out/f"proposal-T{best}-{accepted}.json";path.write_text(json.dumps(proposal,indent=2)+"\n")
                record["proposal"]=str(path.relative_to(ROOT))
                print(json.dumps(dict(event="improvement",T=best,proposal=str(path.relative_to(ROOT)))),flush=True)
            if len(records)%10==0:
                (out/"search.json").write_text(json.dumps(dict(best=best,current=current,evaluated=evaluated,accepted=accepted,records=records,scope="Floating exhaustive coordinate chambers inside cap cone"),indent=2)+"\n")
                print(json.dumps(dict(event="progress",sweep=sweep,coordinates=len(records),evaluated=evaluated,best=best,current=current,elapsed=time.time()-start)),flush=True)
        if time.time()>deadline:break
    report=dict(best=best,current=current,evaluated=evaluated,accepted=accepted,records=records,elapsed=time.time()-start,
        scope="Floating exhaustive coordinate chambers inside cap cone; no global upper bound")
    (out/"search.json").write_text(json.dumps(report,indent=2)+"\n")
    print(json.dumps(dict(event="finished",best=best,current=current,evaluated=evaluated,elapsed=time.time()-start)),flush=True)


if __name__=="__main__":main()
