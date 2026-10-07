"""Walk realizable tangent-grid chirotope cells while retaining a saturated axis.

Triangle mutations are scored combinatorially before LP feasibility is tried.
Floating results are proposals only: independent exact interval validation is
required before a lower-bound claim.  The classical doubling is not modified.
"""
from pathlib import Path
import os
os.environ.setdefault("OMP_NUM_THREADS","1")
os.environ.setdefault("OPENBLAS_NUM_THREADS","1")
import sys,time,itertools as it,json,argparse,random,hashlib,warnings
from fractions import Fraction as F
ROOT=Path(__file__).resolve().parents[3]
sys.path.insert(0,str(ROOT/"work/construction-deps"))
import numpy as np
from scipy import sparse
from scipy.optimize import linprog


def geometry(roots,h,epsilon=1e-10):
    q=len(h);n=q+1;ss=roots.copy();ss[q//2-1]=-epsilon;ss[q//2]=epsilon
    pair_ids={p:i for i,p in enumerate(it.combinations(range(n),2))}
    pairs=list(pair_ids);positions={}
    for (i,j),v in pair_ids.items():
        if i==0:x,y=ss[j-1],0.
        else:
            y=(ss[j-1]-ss[i-1])/(h[i-1]-h[j-1]);x=h[i-1]*y+ss[i-1]
        positions[v]=(x,y)
    rows=[];adj=[set() for _ in pairs];edge_lines={}
    for i in range(n):
        vs=[v for p,v in pair_ids.items() if i in p]
        vs.sort(key=lambda v:positions[v][0 if i==0 else 1])
        rows.append(vs)
        for a,b in zip(vs,vs[1:]):
            adj[a].add(b);adj[b].add(a);edge_lines[tuple(sorted((a,b)))]=i
    triangles=[]
    for a in range(len(pairs)):
        for b,c in it.combinations(sorted(v for v in adj[a] if v>a),2):
            if c in adj[b]:
                labels=tuple(sorted([edge_lines[tuple(sorted(e))] for e in [(a,b),(a,c),(b,c)]]))
                if len(set(labels))==3:triangles.append((labels,tuple(sorted((a,b,c)))))
    return dict(n=n,pairs=pairs,pair_ids=pair_ids,rows=rows,adj=adj,triangles=triangles)


def mutation_score(g,labels):
    i,j,k=labels;rem=set();add=set();ids=g["pair_ids"]
    for line,x,y in [(i,j,k),(j,i,k),(k,i,j)]:
        a=ids[tuple(sorted((line,x)))];b=ids[tuple(sorted((line,y)))];row=g["rows"][line]
        ia=row.index(a);ib=row.index(b)
        if abs(ia-ib)!=1:return None
        if ia>ib:a,b=b,a;ia,ib=ib,ia
        if ia:
            u=row[ia-1];rem.add(tuple(sorted((u,a))));add.add(tuple(sorted((u,b))))
        if ib+1<len(row):
            v=row[ib+1];rem.add(tuple(sorted((b,v))));add.add(tuple(sorted((a,v))))
    return changed_score(g,labels,rem,add)


def parallel_score(g,i,j):
    """The affine chart mutation across a parallel pair, outputs remain simple."""
    vertex=g["pair_ids"][tuple(sorted((i,j)))];rem=set();add=set()
    for line in [i,j]:
        row=g["rows"][line]
        if row[0]==vertex:old,new=row[1],row[-1]
        elif row[-1]==vertex:old,new=row[-2],row[0]
        else:return None
        rem.add(tuple(sorted((vertex,old))));add.add(tuple(sorted((vertex,new))))
    return changed_score(g,(i,j),rem,add)


def changed_score(g,labels,rem,add):
    old=g["adj"];modified={v:set(old[v]) for e in rem|add for v in e}
    for a,b in rem:modified[a].remove(b);modified[b].remove(a)
    for a,b in add:modified[a].add(b);modified[b].add(a)
    def neighbors(v):return modified.get(v,old[v])
    lost={tuple(sorted((a,b,c))) for a,b in rem for c in old[a]&old[b]}
    created={tuple(sorted((a,b,c))) for a,b in add for c in neighbors(a)&neighbors(b)}
    def triangle_labels(vertices):
        p,q,r=[set(g["pairs"][v]) for v in vertices]
        return tuple(sorted([next(iter(p&q)),next(iter(p&r)),next(iter(q&r))]))
    caps_lost=sum(0 in triangle_labels(t) for t in lost)
    caps_created=sum(0 in triangle_labels(t) for t in created)
    return dict(labels=labels,delta=len(created)-len(lost),cap_delta=caps_created-caps_lost,
        lost=sorted(lost),created=sorted(created))


def matrix(roots):
    q=len(roots);pairs=list(it.combinations(range(q),2));triples=list(it.combinations(range(q),3))
    rr=[];cc=[];dd=[]
    for row,(i,j) in enumerate(pairs):rr.extend([row,row]);cc.extend([i,j]);dd.extend([1.,-1.])
    for row,(i,j,k) in enumerate(triples,len(pairs)):
        co=[roots[j]-roots[k],roots[k]-roots[i],roots[i]-roots[j]];scale=max(map(abs,co))
        assert scale>0
        rr.extend([row]*3);cc.extend([i,j,k]);dd.extend(c/scale for c in co)
    return sparse.csr_matrix((dd,(rr,cc)),shape=(len(pairs)+len(triples),q)),{t:len(pairs)+i for i,t in enumerate(triples)},{p:i for i,p in enumerate(pairs)}


def solve(A,sg,limit):
    mat=sparse.hstack([-sparse.diags(sg.astype(float))@A,np.ones((A.shape[0],1))],format="csr")
    obj=np.zeros(A.shape[1]+1);obj[-1]=-1
    with warnings.catch_warnings():
        warnings.simplefilter("ignore")
        result=linprog(obj,A_ub=mat,b_ub=np.zeros(A.shape[0]),bounds=[(-1,1)]*A.shape[1]+[(0,1)],
            method="highs",options={"threads":1,"time_limit":limit,"primal_feasibility_tolerance":1e-9,"dual_feasibility_tolerance":1e-9})
    if result.success and result.x[-1]>1e-9:
        x=result.x[:-1];margin=float(np.min(sg*(A@x)))
        if margin>1e-10:return x,margin
    return None,int(result.status)


def main():
    parser=argparse.ArgumentParser();parser.add_argument("--minutes",type=float,default=30)
    parser.add_argument("--lp-limit",type=float,default=10);parser.add_argument("--seed",type=int,default=107)
    parser.add_argument("--max-neutral",type=int,default=12)
    # A small loss is permitted only as a path to a different cell, never
    # as a retained lower-bound improvement or a formalization target.
    parser.add_argument("--min-delta",type=int,default=0)
    parser.add_argument("--floor",type=int,default=1188)
    parser.add_argument("--max-states",type=int,default=1000)
    parser.add_argument("--parallel-moves",action="store_true")
    args=parser.parse_args()
    out=ROOT/f"research/openmath-seven-hour-2026-10-05/seed_search/facet61-delta{args.min_delta}-seed{args.seed}-parallel{int(args.parallel_moves)}";out.mkdir(parents=True,exist_ok=True)
    source=ROOT/"research/openmath-seven-hour-2026-10-05/constructions/contestant61-refitted-uniform-box.json"
    raw=json.loads(source.read_text());los=list(map(F,raw["lo"]));his=list(map(F,raw["hi"]));vals=[float((a+b)/2) for a,b in zip(los,his)]
    roots=np.array([vals[p]*sgn for p,sgn in raw["labels"][1:]])
    roots[29]=roots[30]=0.
    h=np.array([float(1/F(m)) for m in raw["slopes"][1:]])
    h=(h-np.min(h))/(np.max(h)-np.min(h))*2-1
    A,indices,pair_indices=matrix(roots);sg=np.sign(A@h).astype(np.int8);assert all(sg)
    rng=random.Random(args.seed);start=time.time();deadline=start+args.minutes*60
    seen={hashlib.sha256(sg.tobytes()).hexdigest()};records=[];failed=set();accepted=0;tested=0;best=1190
    states=[(h,sg,0)]
    report=dict(source=str(source.relative_to(ROOT)),source_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),
        scope="Floating chirotope/LP proposals; exact verification required",records=records,best=best)
    state_count=0
    while states and time.time()<deadline and state_count<args.max_states:
        h,sg,depth=states.pop();g=geometry(roots,h)
        state_count+=1
        T=len(g["triangles"]);caps=sum(0 in t for t,v in g["triangles"])
        assert caps==59,(T,caps)
        moves=[]
        for labels,vertices in g["triangles"]:
            if 0 in labels:continue
            score=mutation_score(g,labels)
            if score and score["cap_delta"]==0 and score["delta"]>=args.min_delta and T+score["delta"]>=args.floor:
                row=indices[tuple(i-1 for i in labels)];score["row"]=row;score["distance"]=abs(float((A@h)[row]));moves.append(score)
        if args.parallel_moves:
            order=np.argsort(h)
            for a,b in zip(order,order[1:]):
                labels=tuple(sorted((int(a)+1,int(b)+1)));score=parallel_score(g,*labels)
                if score and score["cap_delta"]==0 and score["delta"]>=args.min_delta and T+score["delta"]>=args.floor:
                    row=pair_indices[tuple(i-1 for i in labels)];score["row"]=row;score["distance"]=abs(float((A@h)[row]));score["kind"]="parallel";moves.append(score)
        rng.shuffle(moves);moves.sort(key=lambda m:(-m["delta"],m["distance"]))
        distribution={str(d):sum(m["delta"]==d for m in moves) for d in sorted({m["delta"] for m in moves})}
        print(json.dumps(dict(event="state",T=T,caps=caps,depth=depth,mutations=distribution,elapsed=time.time()-start)),flush=True)
        neutral=0
        for move in moves:
            if time.time()>deadline:break
            if move["delta"]<=0 and neutral>=args.max_neutral:break
            trial=sg.copy();trial[move["row"]]*=-1;key=hashlib.sha256(trial.tobytes()).hexdigest()
            if key in seen:continue
            seen.add(key);tested+=1
            candidate,status=solve(A,trial,min(args.lp_limit,max(1,deadline-time.time())))
            record=dict(labels=move["labels"],expected_delta=move["delta"],source_T=T,depth=depth,lp=status,passed=candidate is not None)
            records.append(record)
            if candidate is not None:
                gg=geometry(roots,candidate);newT=len(gg["triangles"]);newcaps=sum(0 in t for t,v in gg["triangles"])
                assert newT==T+move["delta"] and newcaps==59,(newT,T,move,newcaps)
                accepted+=1
                proposal=dict(n=61,triangle_screen=newT,caps_screen=newcaps,epsilon_screen="1e-10",
                    reciprocal_slopes=[str(F(float(v+2)).limit_denominator(10**12)) for v in candidate],
                    margin=status,cell_hash=key,parent_source=str(source.relative_to(ROOT)),
                    moved_triple=move["labels"],status="Floating LP proposal; exact true-tangent verification pending")
                if newT>=best:
                    path=out/f"proposal-T{newT}-{accepted:04d}.json";path.write_text(json.dumps(proposal,indent=2)+"\n")
                    record["proposal"]=str(path.relative_to(ROOT))
                if newT>best:
                    best=newT;print(json.dumps(dict(event="improvement",T=newT,margin=status,proposal=str(path.relative_to(ROOT)))),flush=True)
                else:neutral+=1
                states.append((candidate,trial,depth+1))
            if tested%10==0:
                report.update(best=best,tested=tested,accepted=accepted,elapsed=time.time()-start,states=len(states))
                (out/"search.json").write_text(json.dumps(report,indent=2)+"\n")
                print(json.dumps(dict(event="progress",tested=tested,accepted=accepted,best=best,elapsed=time.time()-start)),flush=True)
        report.update(best=best,tested=tested,accepted=accepted,elapsed=time.time()-start,states=len(states))
        (out/"search.json").write_text(json.dumps(report,indent=2)+"\n")
    print(json.dumps(dict(event="finished",best=best,tested=tested,accepted=accepted,elapsed=time.time()-start)),flush=True)


if __name__=="__main__":main()
