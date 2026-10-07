"""Bounded saturated-axis chamber walk using only adjacent-row inequalities.

This is a faster search of the same rigorous linear-realizability domain than
the earlier complete35990-inequality walk. Floating LP output is ONLY a proposal;
no lower bound is promoted until exact true-tangent boxes and Lean replay pass.
"""
from pathlib import Path
import os
os.environ.setdefault('OMP_NUM_THREADS','1');os.environ.setdefault('OPENBLAS_NUM_THREADS','1')
import sys,json,time,random,itertools,hashlib,argparse,importlib.util,warnings,heapq
from fractions import Fraction as F
R=Path(__file__).resolve().parents[3]
sys.path.insert(0,str(R/'work/construction-deps'))
import numpy as np
from scipy import sparse
from scipy.optimize import linprog
spec=importlib.util.spec_from_file_location('priorfacet',R/'experiments/2026-10-05/seed_search/facet_walk61.py')
old=importlib.util.module_from_spec(spec);spec.loader.exec_module(old)

def swapped_rows(g,labels):
    rows=[list(r) for r in g['rows']];i,j,k=labels
    for line,x,y in [(i,j,k),(j,i,k),(k,i,j)]:
        a=g['pair_ids'][tuple(sorted((line,x)))];b=g['pair_ids'][tuple(sorted((line,y)))]
        p=rows[line].index(a);q=rows[line].index(b)
        assert abs(p-q)==1
        rows[line][p],rows[line][q]=rows[line][q],rows[line][p]
    return rows

def constraints(roots,h,g,rows,order=None):
    n=g['n'];q=n-1;required={}
    order=np.argsort(h) if order is None else np.asarray(order)
    ranks=np.empty(len(order),dtype=int);ranks[order]=np.arange(len(order))
    # The desired affine direction order is fixed throughout this walk.
    for i,j in zip(order,order[1:]):required[('pair',int(i),int(j))]=(float(-1),float(1))
    rr=[];cc=[];dd=[];count=0
    for i,j in zip(order,order[1:]):
        rr.extend([count,count]);cc.extend([int(i),int(j)]);dd.extend([-1.,1.]);count+=1
    seen={}
    for line in range(1,n):
        def other(v):
            p=g['pairs'][v];return p[0] if p[1]==line else p[1]
        for va,vb in zip(rows[line],rows[line][1:]):
            j,k=other(va),other(vb)
            if j==0 or k==0:continue # fixed intercept+direction signs give these positions
            inds=[line-1,j-1,k-1]
            co=np.array([roots[j-1]-roots[k-1],roots[k-1]-roots[line-1],roots[line-1]-roots[j-1]])
            den=(ranks[line-1]-ranks[j-1])*(ranks[line-1]-ranks[k-1]);assert den!=0
            co*= -np.sign(den)
            permutation=np.argsort(inds);inds=tuple(inds[z] for z in permutation);co=co[permutation]
            scale=np.max(np.abs(co))
            if scale<1e-15:continue # unavoidable epsilon0 central+axis degeneration
            co=co/scale
            # Repeated adjacent-row constraints are the same oriented triple.
            sign=1 if co[np.argmax(np.abs(co))]>0 else -1
            if inds in seen:
                if seen[inds]!=sign:return None
                continue
            seen[inds]=sign
            rr.extend([count]*3);cc.extend(inds);dd.extend(co.tolist());count+=1
    return sparse.csr_matrix((dd,(rr,cc)),shape=(count,q))

def solve(B,limit):
    if B is None:return None,'inconsistent'
    mat=sparse.hstack([-B,np.ones((B.shape[0],1))],format='csr')
    obj=np.zeros(B.shape[1]+1);obj[-1]=-1
    with warnings.catch_warnings():
        warnings.simplefilter('ignore')
        r=linprog(obj,A_ub=mat,b_ub=np.zeros(B.shape[0]),bounds=[(-1,1)]*B.shape[1]+[(0,1)],method='highs',options={'threads':1,'time_limit':limit,'primal_feasibility_tolerance':1e-9,'dual_feasibility_tolerance':1e-9})
    if r.success and r.x[-1]>1e-9:
        x=r.x[:-1];m=float(np.min(B@x))
        if m>1e-10:return x,m
    return None,int(r.status)

def key(rows,h):return hashlib.sha256(np.asarray(rows,dtype=np.int16).tobytes()+np.argsort(h).astype(np.int8).tobytes()).hexdigest()

def main():
    p=argparse.ArgumentParser();p.add_argument('--minutes',type=float,default=90);p.add_argument('--seed',type=int,default=61003);p.add_argument('--floor',type=int,default=1188);p.add_argument('--max-neutral',type=int,default=20);p.add_argument('--max-states',type=int,default=20000);p.add_argument('--lp-limit',type=float,default=3);p.add_argument('--pilot',action='store_true');p.add_argument('--parallel-moves',action='store_true');a=p.parse_args()
    raw=json.loads((R/'research/openmath-seven-hour-2026-10-05/constructions/contestant61-refitted-uniform-box.json').read_text())
    vals=[float((F(x)+F(y))/2) for x,y in zip(raw['lo'],raw['hi'])]
    roots=np.array([vals[k]*s for k,s in raw['labels'][1:]]);roots[29]=roots[30]=0.
    h=np.array([float(1/F(m)) for m in raw['slopes'][1:]]);h=2*(h-h.min())/(h.max()-h.min())-1
    initial=old.geometry(roots,h);assert len(initial['triangles'])==1190
    B=constraints(roots,h,initial,initial['rows']);x,m=solve(B,a.lp_limit)
    assert x is not None,(m,B.shape)
    gg=old.geometry(roots,x);assert gg['rows']==initial['rows'] and len(gg['triangles'])==1190
    print(json.dumps(dict(event='pilot',constraints=B.shape[0],margin=m,triangles=1190)),flush=True)
    if a.pilot:return
    out=R/f'research/openmath-seven-hour-2026-10-05/constructions/facet-reduced-heap-seed{a.seed}-floor{a.floor}-parallel{int(a.parallel_moves)}';out.mkdir(parents=True,exist_ok=True)
    start=time.time();end=start+60*a.minutes;rng=random.Random(a.seed);seen={key(initial['rows'],h)};states=[(-1190,rng.random(),h,0)];tested=accepted=visited=0;best=1190;records=[]
    while states and time.time()<end and visited<a.max_states:
        _,_,h,depth=heapq.heappop(states);g=old.geometry(roots,h);T=len(g['triangles']);caps=sum(0 in t for t,v in g['triangles']);assert caps==59
        visited+=1;moves=[]
        for labels,vertices in g['triangles']:
            if 0 in labels:continue
            score=old.mutation_score(g,labels)
            if score and score['cap_delta']==0 and T+score['delta']>=a.floor:
                moves.append(score)
        if a.parallel_moves:
            order=np.argsort(h)
            for i,j in zip(order,order[1:]):
                labels=tuple(sorted((int(i)+1,int(j)+1)));score=old.parallel_score(g,*labels)
                if score and score['cap_delta']==0 and T+score['delta']>=a.floor:
                    score['kind']='parallel';moves.append(score)
        rng.shuffle(moves);moves.sort(key=lambda x:-x['delta'])
        neutral=0
        for move in moves:
            if time.time()>=end:break
            if move['delta']<=0 and neutral>=a.max_neutral:continue
            if move.get('kind')=='parallel':
                rows=[list(r) for r in g['rows']];i,j=move['labels'];v=g['pair_ids'][tuple(sorted((i,j)))]
                for line in [i,j]:
                    if rows[line][0]==v:rows[line].pop(0);rows[line].append(v)
                    else:assert rows[line][-1]==v;rows[line].pop();rows[line].insert(0,v)
                order=np.argsort(h).copy();aidx=np.where(order==i-1)[0][0];bidx=np.where(order==j-1)[0][0]
                assert abs(aidx-bidx)==1;order[aidx],order[bidx]=order[bidx],order[aidx]
            else:
                rows=swapped_rows(g,move['labels']);order=np.argsort(h)
            kh=hashlib.sha256(np.asarray(rows,dtype=np.int16).tobytes()+order.astype(np.int8).tobytes()).hexdigest()
            if kh in seen:continue
            seen.add(kh);B=constraints(roots,h,g,rows,order);tested+=1
            x,m=solve(B,min(a.lp_limit,max(0.1,end-time.time())))
            rec=dict(labels=move['labels'],kind=move.get('kind','triangle'),source=T,expected=T+move['delta'],depth=depth,feasible=x is not None,lp=m);records.append(rec)
            if x is not None:
                candidate=old.geometry(roots,x);newT=len(candidate['triangles']);newcaps=sum(0 in t for t,v in candidate['triangles'])
                if candidate['rows']!=rows or newT!=T+move['delta'] or newcaps!=59:
                    rec.update(rejected='Floating row/order/count discrepancy',observed=newT,caps=newcaps);continue
                accepted+=1
                if newT>best:
                    best=newT
                    proposal=dict(n=61,triangle_screen=newT,caps_screen=newcaps,epsilon_screen='1e-10',reciprocal_slopes=[str(F(float(z+2)).limit_denominator(10**12)) for z in x],margin=m,status='Floating LP proposal; exact whole true-tangent interval and Lean checks pending')
                    path=out/f'proposal-T{newT}-{accepted:06d}.json';path.write_text(json.dumps(proposal,indent=2)+'\n');rec['proposal']=str(path.relative_to(R))
                    print(json.dumps(dict(event='improvement',T=newT,path=str(path.relative_to(R)))),flush=True)
                if move['delta']<=0:neutral+=1
                heapq.heappush(states,(-newT,rng.random(),x,depth+1))
            if tested%50==0:
                report=dict(scope='Bounded floating search; not a lower-bound certificate or a global ceiling',best=best,tested=tested,accepted=accepted,visited=visited,queued=len(states),elapsed=time.time()-start,records=records)
                (out/'search.json').write_text(json.dumps(report,indent=2)+'\n')
                print(json.dumps({k:report[k] for k in ['best','tested','accepted','visited','queued','elapsed']}),flush=True)
        if visited%10==0:print(json.dumps(dict(event='state',T=T,depth=depth,visited=visited,tested=tested,best=best)),flush=True)
    report=dict(scope='Bounded floating search; not a lower-bound certificate or a global ceiling',best=best,tested=tested,accepted=accepted,visited=visited,queued=len(states),elapsed=time.time()-start,records=records)
    (out/'search.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(dict(event='finished',best=best,tested=tested,accepted=accepted,visited=visited,elapsed=time.time()-start)),flush=True)
if __name__=='__main__':main()
