"""One-parameter wall sweep of a cubic/quintic dual-curve deformation.

L_i(lambda)=(sin theta_i,cos theta_i,sin3theta_i+lambda*sin(h theta_i)).
At fixed theta every triple determinant is affine in lambda. We sweep its
walls and update only triangle predicates incident to changed vertex pairs.
Floating trigonometry is a proposal generator; improved outputs are replayed
as separate exact rational point arrangements, never asserted as exact true
trigonometric or all-order constructions.
"""
from pathlib import Path
from fractions import Fraction as F
import sys,math,itertools as it,json,time,argparse
ROOT=Path(__file__).resolve().parents[3]
sys.path.insert(0,str(ROOT/'work/construction-deps'))
sys.path.insert(0,str(ROOT/'research/kobon-hybrid'))
sys.path.insert(0,str(Path(__file__).resolve().parent))
import numpy as np
from angular_cubic import data
from exact_geometry import arrangement,primitive

def run(n,harmonic,phase,limit):
    start=time.time();pairs,triples=data(n);N=len(triples);theta=np.array([math.pi*(i+phase)/n for i in range(n)])
    aa=np.sin(theta);bb=np.cos(theta);c0=np.sin(3*theta);c1=np.sin(harmonic*theta)
    base=[];motion=[]
    for i,j,k,*_ in triples:
        wi=-(aa[j]*bb[k]-bb[j]*aa[k]);wj=aa[i]*bb[k]-bb[i]*aa[k];wk=-(aa[i]*bb[j]-bb[i]*aa[j])
        base.append(wi*c0[i]+wj*c0[j]+wk*c0[k]);motion.append(wi*c1[i]+wj*c1[j]+wk*c1[k])
    base=np.array(base);motion=np.array(motion);events=[]
    for r in range(N):
        if abs(motion[r])>1e-12:
            value=-base[r]/motion[r]
            if -limit<value<limit:events.append((float(value),r))
    events.sort();groups=[]
    for value,r in events:
        if groups and abs(value-groups[-1][0])<=1e-10*(1+abs(value)):groups[-1][1].append(r)
        else:groups.append([value,[r]])
    index={tuple(t[:3]):r for r,t in enumerate(triples)};pair_id={p:i for i,p in enumerate(pairs)}
    affected=[]
    for i,j,k,*_ in triples:
        rows=set()
        for a,b in [(i,j),(i,k),(j,k)]:
            rows.update(index[tuple(sorted((a,b,l)))] for l in range(n) if l not in [a,b])
        affected.append(rows)
    positive=[0]*len(pairs);negative=[0]*len(pairs);signs=np.sign(base-limit*motion).astype(np.int8)
    def set_sign(row,s):
        i,j,k,ij,ik,jk=triples[row]
        for pair,label,direction in [(ij,k,s),(ik,j,-s),(jk,i,s)]:
            bit=1<<label
            positive[pair]=(positive[pair]&~bit)|(bit if direction>0 else 0)
            negative[pair]=(negative[pair]&~bit)|(bit if direction<0 else 0)
        signs[row]=s
    for r,s in enumerate(signs):assert s;set_sign(r,int(s))
    def valid(row):
        _,_,_,ij,ik,jk=triples[row]
        return not ((positive[ij]|positive[ik]|positive[jk])&(negative[ij]|negative[ik]|negative[jk]))
    good=[valid(r) for r in range(N)];total=sum(good);best=total;wins=[];history=[]
    baseline=n*(n-3)//3+1+n%2
    out=ROOT/f'research/openmath-seven-hour-2026-10-05/seed_search/harmonic{harmonic}';out.mkdir(parents=True,exist_ok=True)
    def retain(lam,interval):
        nonlocal best
        if total<=best:return
        best=total;item=dict(n=n,harmonic=harmonic,phase=phase,float_T=total,lambda_=lam,interval=interval,current_G=baseline,gain_over_G=total-baseline,raw_min_abs_det=float(np.min(np.abs(base+lam*motion))))
        print(json.dumps(dict(event='best',**item)),flush=True)
        if total>baseline:
            lines=[primitive((F(float(a)).limit_denominator(10**15),F(float(b)).limit_denominator(10**15),F(float(c)).limit_denominator(10**15))) for a,b,c in zip(aa,bb,c0+lam*c1)]
            ar=arrangement(lines);T=len(ar['triangles']);simple=len(ar['points'])==n*(n-1)//2 and all(len(s)==2 for s in ar['points'].values())
            item.update(exact_rational_T=T,exact_simple=simple,lines_frac=[[str(v) for v in l] for l in lines],triangles=[list(t) for t in ar['triangles']],status='Exact rational point arrangement replay; actual harmonic parameter curve and all-order family remain unverified')
            (out/f'n{n:03d}-T{T}-phase{phase:g}-proposal.json').write_text(json.dumps(item,indent=2)+'\n');wins.append(item)
    # Include cubic lambda0 control among checked intervals; no new claim
    # follows from reproducing the retained baseline or an existing record.
    for g,(wall,changed) in enumerate(groups):
        nextwall=groups[g+1][0] if g+1<len(groups) else limit
        lam=(wall+nextwall)/2
        touched=set()
        for r in changed:
            s=1 if base[r]+lam*motion[r]>0 else -1
            if s!=signs[r]:set_sign(r,s);touched.update(affected[r])
        for r in touched:
            value=valid(r);total+=int(value)-int(good[r]);good[r]=value
        retain(lam,[wall,nextwall]);history.append(dict(lambda_=lam,T=total))
    return dict(n=n,harmonic=harmonic,phase=phase,current_G=baseline,best_float=best,walls=len(groups),events=len(events),wins=wins,seconds=time.time()-start,scope='Finite floating wall sweep plus exact rational point replays for improvements; no exact harmonic or universal theorem')

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--orders',nargs='+',type=int,default=[13,18,19,26,31,61]);ap.add_argument('--harmonic',type=int,default=5);ap.add_argument('--phase',type=float,default=1/6);ap.add_argument('--limit',type=float,default=2);args=ap.parse_args();results=[]
    for n in args.orders:
        r=run(n,args.harmonic,args.phase,args.limit);results.append(r);print(json.dumps(dict(event='finish',**r)),flush=True)
        path=ROOT/f'research/openmath-seven-hour-2026-10-05/seed_search/harmonic{args.harmonic}/report-phase{args.phase:g}.json';path.write_text(json.dumps(results,indent=2)+'\n')
