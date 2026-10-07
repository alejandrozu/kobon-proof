"""Tune an exact new-pencil concurrence on a coupled old BBL corridor.

The pencil-pair/corridor crossing equation is solved rationally for kappa.
Two old corridor cores remain exact under rational nullspace reconstruction.
Every point is independently counted; no parametric proof is inferred.
"""
from pathlib import Path
from fractions import Fraction as F
import sys,json,math,itertools as it,time,warnings
ROOT=Path(__file__).resolve().parents[3]
for p in ['experiments/2026-10-02','research/kobon-hybrid','experiments/2026-10-05/corpus']:
    sys.path.insert(0,str(ROOT/p))
sys.path.insert(0,str(Path(__file__).resolve().parent))
from word_grid_fit import tensor
from facet_walk61 import np,matrix,linprog
from fit_optimal31_projective_charts import normalize,dot,cross
from raise_existing_core import exact_nullspace_round
from exact_geometry import arrangement,primitive
from test_backbone_corridor_doubling import profile

if __name__=='__main__':
    start=time.time();source=ROOT/'research/six-hour-2026-09-21/general-bounds/parpalak-utkin-current/certificate-008.json';raw=json.loads(source.read_text());ll=[tuple(map(F,l)) for l in raw['lines_frac']];hs=[(a,b,-c) for a,b,c in ll]+[(F(0),F(0),F(1))];axis=7;corridor=6;entries=[]
    for i,j,k in it.combinations(range(9),3):v=dot(hs[i],cross(hs[j],hs[k]));entries.append(((i,j,k),(v>0)-(v<0)))
    chi=tensor(9,entries);base=normalize(hs,axis,8);ids=[k for a,h,k in base];bid=[k for k in ids if k!=corridor];rank={k:r for r,k in enumerate(bid)};K=next(k for k in range(9) if k not in [axis,8]);d=int(chi[axis,8,K]);aa={k:int(chi[k,axis,8]) for k in ids};signs=np.array([d*int(chi[l,m,8])*aa[l]*aa[m] for l,m in it.combinations(ids,2)]+[int(chi[l,m,k])*aa[l]*aa[m]*aa[k] for l,m,k in it.combinations(ids,3)]);strict=np.where(signs!=0)[0];equals=np.where(signs==0)[0]
    regular=[-math.sqrt(3),-1/math.sqrt(3),0.,0.,1/math.sqrt(3),math.sqrt(3)];eps=F(1,10000);triples=list(it.combinations(range(7),3));pairs=list(it.combinations(range(7),2));newroots=[F(math.tan(math.pi*k/12)).limit_denominator(10**15) for k in [-5,-3,-1,1,3,5]]
    out=ROOT/'research/openmath-seven-hour-2026-10-05/seed_search/backbone-corridor-core-event';out.mkdir(parents=True,exist_ok=True);records=[];wins=[];best=0
    for magnitude in [10,100,1000,10000,100000,1000000,10000000]:
        a=F(-magnitude);roots=np.array([regular[rank[k]] if k!=corridor else float(a) for k in ids]);A,_,_=matrix(roots);Ad=A.toarray();M=np.column_stack([-signs[strict,None]*Ad[strict],np.ones(len(strict))]);E=np.column_stack([Ad[equals],np.zeros(len(equals))]);obj=np.zeros(8);obj[-1]=-1
        with warnings.catch_warnings():
            warnings.simplefilter('ignore');lp=linprog(obj,A_ub=M,b_ub=np.zeros(len(M)),A_eq=E,b_eq=np.zeros(len(E)),bounds=[(-1,1)]*7+[(0,1)],method='highs',options={'threads':1})
        margin=float(lp.x[-1]) if lp.success else 0
        if margin<1e-10:continue
        vals=[F(float(v)).limit_denominator(10**12) for v in lp.x[:-1]]
        if vals[ids.index(bid[2])]<vals[ids.index(bid[3])]:vals=[-v for v in vals]
        vals=[v+2 for v in vals];rr=[F(float(v)).limit_denominator(10**15) for v in roots]
        for k in bid:
            if rank[k]==2:rr[ids.index(k)]=-eps
            if rank[k]==3:rr[ids.index(k)]=eps
        EF=[]
        for row in equals:
            i,j,k=triples[row-len(pairs)];coef=[F(0)]*7;coef[i]=rr[j]-rr[k];coef[j]=rr[k]-rr[i];coef[k]=rr[i]-rr[j];EF.append(coef)
        vals=exact_nullspace_round(EF,vals);old=[(F(0),F(1),F(0))]+[(F(1),-h,t) for h,t in zip(vals,rr)];ci=ids.index(corridor)+1;h=vals[ci-1]
        assert len(arrangement(old)['triangles'])==15
        for i,j in it.combinations(range(6),2):
            ti,tj=newroots[i],newroots[j];fi,fj=2*ti/(1+ti*ti),2*tj/(1+tj*tj);gi,gj=1/ti,1/tj;N0=fi*(ti-a)-fj*(tj-a);N1=gi*(ti-a)-gj*(tj-a)
            if not N1:continue
            delta0=-N0/N1
            if delta0<=0 or delta0>F(1,1000):continue
            for direction in [1,-1]:
                for power in [12,20,30]:
                    delta=delta0*(1+F(direction,10**power));Fi,Fj=fi+delta*gi,fj+delta*gj;N=Fi*(ti-a)-Fj*(tj-a);den=h*Fi*Fj*(ti-tj)
                    if not den:continue
                    kappa=N/den
                    if kappa<=0 or kappa>delta*eps:continue
                    added=[(m,F(-1),m*t) for t in newroots for m in [kappa*(2*t/(1+t*t)+delta/t)]];lines=list(map(primitive,old+added));p=profile(lines,ci);r=p['ledger'];rec=dict(magnitude=magnitude,margin=margin,pair=[i,j],delta0=str(delta0),delta=str(delta),kappa=str(kappa),direction=direction,power=power,**p);records.append(rec)
                    if r and r['T']>best:best=r['T'];print(json.dumps(dict(event='best',**rec)),flush=True)
                    if r and r['T']>=54:
                        dst=out/f'A{magnitude}-pair{i}_{j}-p{power}-T{r["T"]}.json';dst.write_text(json.dumps(dict(rec,corridor_index=ci,lines_frac=[[str(v) for v in l] for l in lines],source=str(source.relative_to(ROOT)),status_note='Exact new-core event point; no true-tangent uniformity or scalable theorem proved'),indent=2)+'\n');wins.append(str(dst.relative_to(ROOT)))
    report=dict(best=best,records=records,wins=wins,seconds=time.time()-start,scope='Exact concurrence-event points on a fixed coupled BBL type; no infinite or SOTA claim')
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(dict(best=best,wins=len(wins),tested=len(records),seconds=report['seconds'])),flush=True)
