"""Exact combinatorial screens of nonuniform angular samples of the FP cubic.

Angles are theta_i=pi*(i+alpha[i mod p])/n with 0<alpha<1. The existing
Furedi--Palasti determinant factorization makes every triple sign an exact
integer sum-angle comparison. This is an external finite counter, not a Lean
all-order triangle-count theorem. Periodicity is retained for later scalable
count analysis if a stronger candidate is found.
"""
from pathlib import Path
from functools import lru_cache
from fractions import Fraction as F
import itertools as it,json,random,time,argparse,sys
ROOT=Path(__file__).resolve().parents[3]

@lru_cache(None)
def data(n):
    pairs=list(it.combinations(range(n),2));ids={p:i for i,p in enumerate(pairs)}
    triples=[(i,j,k,ids[i,j],ids[i,k],ids[j,k]) for i,j,k in it.combinations(range(n),3)]
    return pairs,triples

def count_scaled(n,xs,den,return_list=False,projective=False):
    pairs,triples=data(n);positive=[0]*len(pairs);negative=[0]*len(pairs)
    for i,j,k,ij,ik,jk in triples:
        total=xs[i]+xs[j]+xs[k]
        if total%den==0:return None
        s=(total//den)%2==0
        (positive if s else negative)[ij]|=1<<k
        (negative if s else positive)[ik]|=1<<j
        (positive if s else negative)[jk]|=1<<i
    selected=[];count=0
    for i,j,k,ij,ik,jk in triples:
      for flip_ik,flip_jk in ([(False,False),(False,True),(True,False),(True,True)] if projective else [(False,False)]):
        p_ik,n_ik=(negative[ik],positive[ik]) if flip_ik else (positive[ik],negative[ik])
        p_jk,n_jk=(negative[jk],positive[jk]) if flip_jk else (positive[jk],negative[jk])
        if not ((positive[ij]|p_ik|p_jk)&(negative[ij]|n_ik|n_jk)):
            count+=1
            if return_list:selected.append(dict(lines=[i,j,k],vertex_lift_signs=[1,-1 if flip_ik else 1,-1 if flip_jk else 1]) if projective else [i,j,k])
    return (count,selected) if return_list else count

def triangles(n,offsets,D=1000003,return_list=False):
    p=len(offsets);xs=[i*D+offsets[i%p] for i in range(n)]
    return count_scaled(n,xs,n*D,return_list)

def gap_triangles(n,gaps,return_list=False,projective=False,phase=1):
    # theta_i=pi*(6*prefix_i+1)/(6*total_n). Every triple numerator is3 mod6,
    # so no triple is concurrent for ANY order or positive integer gap pattern.
    prefix=[0]
    for i in range(n):prefix.append(prefix[-1]+gaps[i%len(gaps)])
    xs=[6*p+phase for p in prefix[:-1]]
    return count_scaled(n,xs,6*prefix[-1],return_list,projective)

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--seconds',type=float,default=180);ap.add_argument('--seed',type=int,default=6319);ap.add_argument('--orders',nargs='+',type=int,default=[13,18,19,26,31]);ap.add_argument('--mode',choices=['offsets','gaps'],default='offsets');args=ap.parse_args();rng=random.Random(args.seed);D=1000003;start=time.time();deadline=start+args.seconds
    out=ROOT/f'research/openmath-seven-hour-2026-10-05/seed_search/angular-cubic-{args.mode}';out.mkdir(parents=True,exist_ok=True);best={};records=[];trials=0
    control=[166667] if args.mode=='offsets' else [1]
    counter=(lambda n,a,details=False: triangles(n,a,D,details)) if args.mode=='offsets' else gap_triangles
    for n in args.orders:
        t=counter(n,control);expected=n*(n-3)//3+1;assert t==expected,(n,t,expected)
        best[n]=dict(T=t,period=1,offset_numerators=control,denominator=D,trial='uniformcontrol',current_G=n*(n-3)//3+1+n%2)
    def test(offsets,tag):
        nonlocal trials
        trials+=1;p=len(offsets)
        for n in args.orders:
            t=counter(n,offsets)
            if t is None:return
            if t>best[n]['T']:
                record=dict(n=n,T=t,period=p,offset_numerators=offsets.copy(),denominator=D,trial=tag,current_G=n*(n-3)//3+1+n%2,gain_over_G=t-(n*(n-3)//3+1+n%2),status='Exact sum-angle/chirotope finite count; actual Lean witness and scalable formula not yet established')
                best[n]=record;records.append(record);print(json.dumps(dict(event='best',**record)),flush=True)
                count,ts=counter(n,offsets,True);record['triangles']=ts;record['parameter_mode']=args.mode
                (out/f'n{n:03d}-T{t}-period{p}-proposal.json').write_text(json.dumps(record,indent=2)+'\n')
    for p in [2,3,4,6,8,12]:
        patterns=[[int(D*(r+0.5)/p) for r in range(p)],[int(D*(0.05 if r%2 else 0.95)) for r in range(p)],[int(D*(0.1 if r%3 else 0.9)) for r in range(p)]] if args.mode=='offsets' else [[r+1 for r in range(p)],[1 if r%2 else 3 for r in range(p)],[1 if r%3 else 5 for r in range(p)]]
        for pattern in patterns:test(pattern,'structuredpattern')
    while time.time()<deadline:
        p=rng.choice([2,3,4,6,8,12]);offsets=[rng.randrange(1,D) for _ in range(p)] if args.mode=='offsets' else [rng.randint(1,20) for _ in range(p)];test(offsets,f'randomseed{args.seed}-trial{trials}')
    result=dict(best=list(best.values()),trials=trials,records=records,seconds=time.time()-start,source_identity='Kobon/FurediPalasti.lean eval_line; no new curve identity assumed',scope='Finite exact periodic nonuniform angular sample search. No all-order theorem or global optimum inferred.')
    (out/'report.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(dict(trials=trials,best=list(best.values()),seconds=time.time()-start)),flush=True)

if __name__=='__main__':main()
