"""Fit an optimal 13-line backbone with its actual 14-line optimal corridor.

This targets known Maiorana09 and Parpalak--Utkin fourteen-line types, rather
than repeating the failed particular q6-generated thirteen-line type.
Finite epsilon LP fits are screened at two scales; positive fits receive exact
equality reconstruction and a first controlled BBL doubling replay.
"""
from pathlib import Path
from fractions import Fraction as F
import json,math,sys,itertools as it,time,warnings
ROOT=Path(__file__).resolve().parents[3]
for p in ['research/kobon-hybrid','experiments/2026-10-02','experiments/2026-10-05/corpus']:
    sys.path.insert(0,str(ROOT/p))
sys.path.insert(0,str(Path(__file__).resolve().parent))
from word_grid_fit import tensor
from facet_walk61 import np,matrix,linprog
from fit_optimal31_projective_charts import normalize,dot,cross
from raise_existing_core import exact_nullspace_round
from exact_geometry import arrangement,primitive
from check_global_token_hypotheses import ledger
from test_backbone_corridor_doubling import pencil,profile

if __name__=='__main__':
    start=time.time();sources=[ROOT/'research/six-hour-2026-09-21/general-bounds/maiorana14/certificate-09.json',ROOT/'research/six-hour-2026-09-21/general-bounds/parpalak-utkin-current/certificate-014.json'];out=ROOT/'research/openmath-seven-hour-2026-10-05/seed_search/larger-backbone-corridors';out.mkdir(parents=True,exist_ok=True);records=[];wins=[];best=0;q=12
    for source in sources:
        raw=json.loads(source.read_text());ll=[tuple(map(F,l)) for l in raw['lines_frac']];ar=arrangement(ll);cores=[p for p,s in ar['points'].items() if len(s)>=3];corridor=next(iter(set.intersection(*(set(ar['points'][p]) for p in cores))));labels=[i for i in range(14) if i!=corridor];old=arrangement([ll[i] for i in labels]);sat=[labels[i] for i in range(13) if sum(i in t for t in old['triangles'])==11];assert len(old['triangles'])==47
        hs=[(a,b,-c) for a,b,c in ll]+[(F(0),F(0),F(1))];entries=[]
        for i,j,k in it.combinations(range(15),3):v=dot(hs[i],cross(hs[j],hs[k]));entries.append(((i,j,k),(v>0)-(v<0)))
        chi=tensor(15,entries)
        for axis in sat:
            base=normalize(hs,axis,14);ids=[k for a,h,k in base];bid=[k for k in ids if k!=corridor];sa={k:a for a,h,k in base};rank={k:r for r,k in enumerate(bid)};pos=sum(sa[k]<sa[corridor] for k in bid);eq=next((k for k in bid if sa[k]==sa[corridor]),None);K=next(k for k in range(15) if k not in [axis,14]);d=int(chi[axis,14,K]);aa={k:int(chi[k,axis,14]) for k in ids};sg=[d*int(chi[l,m,14])*aa[l]*aa[m] for l,m in it.combinations(ids,2)]+[int(chi[l,m,k])*aa[l]*aa[m]*aa[k] for l,m,k in it.combinations(ids,3)];signs=np.array(sg);strict=np.where(signs!=0)[0];equals=np.where(signs==0)[0]
            for eps in [F(1,1000),F(1,1000000)]:
                regular=[math.tan(math.pi*k/q) for k in range(-q//2+1,0)]+[-float(eps),float(eps)]+[math.tan(math.pi*k/q) for k in range(1,q//2)]
                if eq is not None:choices=[regular[rank[eq]]]
                elif pos==0:choices=[-5.,-10.,-100.]
                elif pos==q:choices=[5.,10.,100.]
                else:choices=[regular[pos-1]*s+regular[pos]*(1-s) for s in [.25,.5,.75]]
                for croot in choices:
                    roots=np.array([regular[rank[k]] if k!=corridor else croot for k in ids]);A,_,_=matrix(roots);Ad=A.toarray();M=np.column_stack([-signs[strict,None]*Ad[strict],np.ones(len(strict))]);E=np.column_stack([Ad[equals],np.zeros(len(equals))]);obj=np.zeros(14);obj[-1]=-1
                    with warnings.catch_warnings():
                        warnings.simplefilter('ignore');lp=linprog(obj,A_ub=M,b_ub=np.zeros(len(M)),A_eq=E,b_eq=np.zeros(len(E)),bounds=[(-1,1)]*13+[(0,1)],method='highs',options={'threads':1,'time_limit':5})
                    margin=float(lp.x[-1]) if lp.success else 0;rec=dict(source=str(source.relative_to(ROOT)),axis=axis,corridor=corridor,croot=croot,eps=str(eps),position=pos,equal_rank=rank[eq] if eq is not None else None,margin=margin,status=int(lp.status),passed=False);records.append(rec)
                    if margin<1e-9:continue
                    vals=[F(float(x)).limit_denominator(10**12) for x in lp.x[:-1]]
                    if vals[ids.index(bid[5])]<vals[ids.index(bid[6])]:vals=[-v for v in vals]
                    vals=[v+2 for v in vals];rr=[F(float(a)).limit_denominator(10**15) for a in roots]
                    for k in bid:
                        if rank[k]==5:rr[ids.index(k)]=-eps
                        if rank[k]==6:rr[ids.index(k)]=eps
                    if eq is not None:rr[ids.index(corridor)]=rr[ids.index(eq)]
                    triples=list(it.combinations(range(13),3));pairs=list(it.combinations(range(13),2));EF=[]
                    for row in equals:
                        assert row>=len(pairs);i,j,k=triples[row-len(pairs)];co=[F(0)]*13;co[i]=rr[j]-rr[k];co[j]=rr[k]-rr[i];co[k]=rr[i]-rr[j];EF.append(co)
                    vals=exact_nullspace_round(EF,vals);lines=[(F(0),F(1),F(0))]+[(F(1),-h,a) for h,a in zip(vals,rr)];ci=ids.index(corridor)+1;r=ledger(lines)
                    if not r or r['T']!=54:continue
                    rec.update(passed=True,source_ledger=r)
                    for delta in [eps/10,eps/10000]:
                        doubled=lines+pencil(q,delta,delta*eps**2);p=profile(doubled,ci);rec.setdefault('doubling',[]).append(dict(delta=str(delta),**p))
                        if p['ledger'] and p['ledger']['T']>best:best=p['ledger']['T'];print(json.dumps(dict(event='best',best=best,**rec)),flush=True)
                    dst=out/f'{source.parent.name}-axis{axis}-eps{eps.denominator}-root{croot}.json';dst.write_text(json.dumps(dict(rec,corridor_index=ci,source_labels=[axis]+ids,lines_frac=[[str(v) for v in l] for l in lines],status_note='Exact finite fitted coupled14/54; uniformity and recurrence remain unproved'),indent=2)+'\n');wins.append(str(dst.relative_to(ROOT)))
    (out/'report.json').write_text(json.dumps(dict(records=records,wins=wins,best_doubling=best,seconds=time.time()-start,scope='Known fourteen-line sources, all saturated backbone axes and bounded root choices/two epsilon scales'),indent=2)+'\n');print(json.dumps(dict(LPs=len(records),fits=len(wins),best=best,seconds=time.time()-start)),flush=True)
