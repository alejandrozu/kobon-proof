"""Fit8/15 with its7/11 backbone on the actual q6 BBL intercept grid.

The corridor is an extra graph line, with exact concurrence constraints at
its two old ordinary vertices. Saturated backbone axes, not the corridor axis,
are the BBL distinguished axes. Fixed-limit LP data are reconstructed in an
exact rational nullspace at positive epsilon before every geometry replay.
"""
from pathlib import Path
from fractions import Fraction as F
import sys,itertools as it,json,time,math,warnings
ROOT=Path(__file__).resolve().parents[3];sys.path.insert(0,str(ROOT/'experiments/2026-10-02'));sys.path.insert(0,str(Path(__file__).resolve().parent));sys.path.insert(0,str(ROOT/'research/kobon-hybrid'));sys.path.insert(0,str(ROOT/'experiments/2026-10-05/corpus'))
from word_grid_fit import tensor
from facet_walk61 import np,matrix,linprog
from fit_optimal31_projective_charts import normalize,dot,cross
from raise_existing_core import exact_nullspace_round
from exact_geometry import arrangement,primitive
from check_global_token_hypotheses import ledger

if __name__=='__main__':
    start=time.time();source=ROOT/'research/six-hour-2026-09-21/general-bounds/parpalak-utkin-current/certificate-008.json';raw=json.loads(source.read_text());ll=[tuple(map(F,l)) for l in raw['lines_frac']];ar=arrangement(ll);cores=[p for p,s in ar['points'].items() if len(s)==3];corridor=next(iter(set.intersection(*(set(ar['points'][p]) for p in cores))));old_labels=[i for i in range(8) if i!=corridor];old=arrangement([ll[i] for i in old_labels]);SAT=[old_labels[i] for i in range(7) if sum(i in t for t in old['triangles'])==5]
    hs=[(a,b,-c) for a,b,c in ll]+[(F(0),F(0),F(1))];entries=[]
    for i,j,k in it.combinations(range(9),3):
        v=dot(hs[i],cross(hs[j],hs[k]));entries.append(((i,j,k),(v>0)-(v<0)))
    chi=tensor(9,entries);out=ROOT/'research/openmath-seven-hour-2026-10-05/seed_search/backbone-corridor-bbl';out.mkdir(parents=True,exist_ok=True);reports=[];seeds=[]
    regular=[-math.sqrt(3),-1/math.sqrt(3),0.,0.,1/math.sqrt(3),math.sqrt(3)];eps=F(1,10000)
    for axis in SAT:
        base=normalize(hs,axis,8);ids=[k for a,h,k in base];backbone_ids=[k for a,h,k in base if k!=corridor];source_a={k:a for a,h,k in base};oldrank={k:r for r,k in enumerate(backbone_ids)}
        coincident=next((k for k in backbone_ids if source_a[k]==source_a[corridor]),None)
        if coincident is not None:
            if oldrank[coincident] in [2,3]:
                reports.append(dict(axis=axis,passed=False,reason='Corridor coincides with a special root; constant-h strict limit has three merged graph roots'))
                continue
            choices=[None]
        else:
            sign=-1 if source_a[corridor]<min(source_a[k] for k in backbone_ids) else 1
            assert sign==-1 or source_a[corridor]>max(source_a[k] for k in backbone_ids)
            choices=[sign*r for r in [2,3,5,10]]
        K=next(k for k in range(9) if k not in [axis,8]);d=int(chi[axis,8,K]);aa={k:int(chi[k,axis,8]) for k in ids};signs=[d*int(chi[l,m,8])*aa[l]*aa[m] for l,m in it.combinations(ids,2)]+[int(chi[l,m,k])*aa[l]*aa[m]*aa[k] for l,m,k in it.combinations(ids,3)];signs=np.array(signs)
        for croot in choices:
            roots=np.array([regular[oldrank[k]] if k!=corridor else regular[oldrank[coincident]] if coincident is not None else croot for k in ids]);A,_,_=matrix(roots);Ad=A.toarray();strict=np.where(signs!=0)[0];equal=np.where(signs==0)[0];M=np.column_stack([-signs[strict,None]*Ad[strict],np.ones(len(strict))]);E=np.column_stack([Ad[equal],np.zeros(len(equal))]);objective=np.zeros(8);objective[-1]=-1
            with warnings.catch_warnings():
                warnings.simplefilter('ignore');lp=linprog(objective,A_ub=M,b_ub=np.zeros(len(M)),A_eq=E,b_eq=np.zeros(len(E)),bounds=[(-1,1)]*7+[(0,1)],method='highs',options={'threads':1,'time_limit':10})
            margin=float(lp.x[-1]) if lp.success else None;record=dict(axis=axis,corridor=corridor,coincident_source_line=coincident,corridor_root=croot,margin=margin,status=int(lp.status),passed=False)
            if margin and margin>1e-9:
                vals=[F(float(x)).limit_denominator(10**12) for x in lp.x[:-1]];back_h=[vals[ids.index(k)] for k in backbone_ids]
                if back_h[2]<back_h[3]:vals=[-v for v in vals]
                vals=[v+2 for v in vals]
                rr=[F(float(a)).limit_denominator(10**15) for a in roots]
                for k in backbone_ids:
                    rank=oldrank[k]
                    if rank==2:rr[ids.index(k)]=-eps
                    if rank==3:rr[ids.index(k)]=eps
                triples=list(it.combinations(range(7),3));pairs=list(it.combinations(range(7),2));EF=[]
                for row in equal:
                    assert row>=len(pairs)
                    i,j,k=triples[row-len(pairs)];coef=[F(0)]*7;coef[i]=rr[j]-rr[k];coef[j]=rr[k]-rr[i];coef[k]=rr[i]-rr[j];EF.append(coef)
                vals=exact_nullspace_round(EF,vals);lines=[(F(0),F(1),F(0))]+[(F(1),-h,a) for h,a in zip(vals,rr)];corridor_index=ids.index(corridor)+1;prev=[l for i,l in enumerate(lines) if i!=corridor_index];r=ledger(lines);Tprev=len(arrangement(prev)['triangles'])
                if r and r['T']==15 and r['multiplicities']=={3:2} and Tprev==11:
                    record.update(passed=True,exact_ledger=r,backbone_T=Tprev);seed=dict(record,n=8,q=6,source=str(source.relative_to(ROOT)),backbone_indices=[i for i in range(8) if i!=corridor_index],corridor_index=corridor_index,source_labels=[axis]+ids,epsilon=str(eps),lines_frac=[[str(v) for v in l] for l in lines],status_note='Exact rational coupled8/15 and7/11 point with genuine BBL root layout; actual tangent uniform parameter and corridor transfer theorem pending');p=out/f'seed-axis{axis}-root{croot}.json';p.write_text(json.dumps(seed,indent=2)+'\n');record['seed']=str(p.relative_to(ROOT));seeds.append(record);print(json.dumps(dict(event='seed',**record)),flush=True)
            reports.append(record)
    (out/'fit-report.json').write_text(json.dumps(dict(saturated_backbone_axes=SAT,records=reports,seeds=seeds,seconds=time.time()-start,scope='Bounded actual-type coupled BBL backbone/corridor fitting, no iteration claim'),indent=2)+'\n');print(json.dumps(dict(SAT=SAT,seeds=len(seeds),seconds=time.time()-start)),flush=True)
