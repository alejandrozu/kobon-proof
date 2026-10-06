"""Fit distinct exact 8/15 corridor types to a q6 BBL simple backbone.

Inputs are credited physical subsets of Maiorana's fourteen-line certificates.
Duplicate normalized signed types are skipped. Finite rational reconstruction
preserves both triple equalities; a q6 pencil is then independently recounted.
"""
from pathlib import Path
from fractions import Fraction as F
import json,math,sys,itertools as it,time,warnings,hashlib
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
    start=time.time();folder=ROOT/'research/openmath-seven-hour-2026-10-05/corpus/corridor-subarrangements';out=ROOT/'research/openmath-seven-hour-2026-10-05/seed_search/backbone-corridor-alternative';out.mkdir(parents=True,exist_ok=True)
    records=[];seen=set();wins=[];regular=[-math.sqrt(3),-1/math.sqrt(3),0.,0.,1/math.sqrt(3),math.sqrt(3)];eps=F(1,10000);best=0
    for source in sorted(folder.glob('M*.json')):
        raw=json.loads(source.read_text());ll=[tuple(map(F,l)) for l in raw['lines_frac']];ar=arrangement(ll);cores=[p for p,s in ar['points'].items() if len(s)>=3]
        if len(cores)!=2 or any(len(ar['points'][p])!=3 for p in cores):continue
        common=set.intersection(*(set(ar['points'][p]) for p in cores))
        if len(common)!=1:continue
        corridor=next(iter(common));labels=[i for i in range(8) if i!=corridor];old=arrangement([ll[i] for i in labels]);sat=[labels[i] for i in range(7) if sum(i in t for t in old['triangles'])==5]
        if len(old['triangles'])!=11:continue
        hs=[(a,b,-c) for a,b,c in ll]+[(F(0),F(0),F(1))];entries=[]
        for i,j,k in it.combinations(range(9),3):v=dot(hs[i],cross(hs[j],hs[k]));entries.append(((i,j,k),(v>0)-(v<0)))
        chi=tensor(9,entries)
        for axis in sat:
            base=normalize(hs,axis,8);ids=[k for a,h,k in base];bid=[k for a,h,k in base if k!=corridor];sa={k:a for a,h,k in base};rank={k:r for r,k in enumerate(bid)}
            pos=sum(sa[k]<sa[corridor] for k in bid);equal=next((k for k in bid if sa[k]==sa[corridor]),None)
            K=next(k for k in range(9) if k not in [axis,8]);d=int(chi[axis,8,K]);aa={k:int(chi[k,axis,8]) for k in ids}
            sg=[d*int(chi[l,m,8])*aa[l]*aa[m] for l,m in it.combinations(ids,2)]+[int(chi[l,m,k])*aa[l]*aa[m]*aa[k] for l,m,k in it.combinations(ids,3)]
            key=(pos,rank[equal] if equal is not None else -1,tuple(sg))
            if key in seen:continue
            seen.add(key)
            if equal is not None:
                if rank[equal] in [2,3]:continue
                choices=[regular[rank[equal]]]
            elif pos==0:choices=[-2.,-5.,-10.]
            elif pos==6:choices=[2.,5.,10.]
            elif pos==3:choices=[0.]
            else:choices=[regular[pos-1]*s+regular[pos]*(1-s) for s in [.25,.5,.75]]
            signs=np.array(sg);strict=np.where(signs!=0)[0];equals=np.where(signs==0)[0]
            for croot in choices:
                roots=np.array([regular[rank[k]] if k!=corridor else croot for k in ids]);A,_,_=matrix(roots);Ad=A.toarray();M=np.column_stack([-signs[strict,None]*Ad[strict],np.ones(len(strict))]);E=np.column_stack([Ad[equals],np.zeros(len(equals))]);objective=np.zeros(8);objective[-1]=-1
                with warnings.catch_warnings():
                    warnings.simplefilter('ignore');lp=linprog(objective,A_ub=M,b_ub=np.zeros(len(M)),A_eq=E,b_eq=np.zeros(len(E)),bounds=[(-1,1)]*7+[(0,1)],method='highs',options={'threads':1,'time_limit':5})
                margin=float(lp.x[-1]) if lp.success else 0.;rec=dict(source=str(source.relative_to(ROOT)),axis=axis,corridor=corridor,croot=croot,position=pos,equal_rank=rank[equal] if equal is not None else None,margin=margin,status=int(lp.status),passed=False);records.append(rec)
                if margin<1e-9:continue
                vals=[F(float(x)).limit_denominator(10**12) for x in lp.x[:-1]]
                if vals[ids.index(bid[2])]<vals[ids.index(bid[3])]:vals=[-v for v in vals]
                vals=[v+2 for v in vals];rr=[F(float(a)).limit_denominator(10**15) for a in roots]
                for k in bid:
                    if rank[k]==2:rr[ids.index(k)]=-eps
                    if rank[k]==3:rr[ids.index(k)]=eps
                triples=list(it.combinations(range(7),3));pairs=list(it.combinations(range(7),2));EF=[]
                for row in equals:
                    assert row>=len(pairs);i,j,k=triples[row-len(pairs)];co=[F(0)]*7;co[i]=rr[j]-rr[k];co[j]=rr[k]-rr[i];co[k]=rr[i]-rr[j];EF.append(co)
                vals=exact_nullspace_round(EF,vals);lines=[(F(0),F(1),F(0))]+[(F(1),-h,a) for h,a in zip(vals,rr)];ci=ids.index(corridor)+1
                r=ledger(lines)
                if not r or r['T']!=15 or r['multiplicities']!={3:2}:continue
                rec.update(passed=True,source_ledger=r)
                for delta in [F(1,1000),F(1,1000000)]:
                    doubled=lines+pencil(6,delta,delta*eps**2);p=profile(doubled,ci);rec.setdefault('doubling',[]).append(dict(delta=str(delta),**p))
                    if p['ledger'] and p['ledger']['T']>best:
                        best=p['ledger']['T'];print(json.dumps(dict(event='best',best=best,**rec)),flush=True)
                    if p['ledger'] and p['ledger']['T']>=54:
                        dst=out/f'candidate{len(wins)}-T{p["ledger"]["T"]}.json';dst.write_text(json.dumps(dict(rec,**p,corridor_index=ci,lines_frac=[[str(v) for v in l] for l in doubled],status_note='Exact coupled BBL point; tangent uniformity and iteration not yet proved',attribution='Seed is a physical subset of Andrea Maiorana CC-BY4.0 fourteen-line certificate; source path pinned in source artifact'),indent=2)+'\n');wins.append(str(dst.relative_to(ROOT)))
    report=dict(unique_types=len(seen),records=records,best=best,wins=wins,seconds=time.time()-start,scope='Distinct available 8-line affine types and bounded BBL point controls, no exhaustive geometric impossibility claim')
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(dict(types=len(seen),LPs=len(records),best=best,wins=wins,seconds=report['seconds'])),flush=True)
