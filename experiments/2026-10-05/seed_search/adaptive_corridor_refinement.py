"""Adaptive singular-root refinement preserving the actual old corridor type.

One duplicate-root pair moves together by a half-grid slot. Old chirotope signs
are preserved through an exact linear-form model. Every new axis interval is
required to have a cap, including all8 side-phase choices at the two cores.
LP outputs are proposals followed by exact rational point replays; an
infinite geometric shape invariant is not assumed.
"""
from pathlib import Path
from fractions import Fraction as F
import sys,itertools as it,json,time,math,argparse,warnings
ROOT=Path(__file__).resolve().parents[3];sys.path.insert(0,str(ROOT/'work/construction-deps'));sys.path.insert(0,str(Path(__file__).resolve().parent));sys.path.insert(0,str(ROOT/'research/kobon-hybrid'));sys.path.insert(0,str(ROOT/'experiments/2026-10-05/corpus'))
from facet_walk61 import np,matrix,linprog,sparse
from exact_geometry import arrangement,primitive
from check_global_token_hypotheses import ledger

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--source',default='research/openmath-seven-hour-2026-10-05/seed_search/singular-corridor-grid/n014-sourcemaiorana14-certificate-02-proposal.json');ap.add_argument('--tag',default='adaptive-corridor24');args=ap.parse_args();start=time.time();source=ROOT/args.source;raw=json.loads(source.read_text());q=raw['q'];qnext=2*q;oldgroups=raw['root_group_indices'];h0=np.array(list(map(lambda x:float(F(x)),raw['reciprocal_slopes'])));oldroots=np.array([math.tan(math.pi*(g-(q//2-1))/q) for g in oldgroups]);A0,_,_=matrix(oldroots);sg=np.sign(A0@h0);assert all(sg)
    duplicated=raw['duplicate_ranks'];assert len(duplicated)==2 and duplicated[1]==duplicated[0]+1
    refinements=[]
    for shifted in duplicated:
      for shift in [-1,1]:
        mapping={g:2*g+1 for g in range(q-1)};mapping[shifted]+=shift
        if len(set(mapping.values()))!=q-1:continue
        targetduplicates=[mapping[g] for g in duplicated]
        # All old two-core geometry is retained. Adjacency is chosen as a
        # candidate shape condition, not asserted as a necessary theorem.
        if abs(targetduplicates[0]-targetduplicates[1])!=1:continue
        parentpositions=[mapping[g] for g in oldgroups];labels=[(group,old) for old,group in enumerate(parentpositions)];selected=set(parentpositions)
        labels += [(g,None) for g in range(qnext-1) if g not in selected];labels.sort(key=lambda t:(t[0],-1 if t[1] is None else t[1]));d=len(labels);assert d==qnext+1
        old_to_new={old:j for j,(group,old) in enumerate(labels) if old is not None};roots=np.array([math.tan(math.pi*(group-(qnext//2-1))/qnext) for group,old in labels]);Aold,_,_=matrix(np.array([roots[old_to_new[i]] for i in range(len(oldgroups))]));Aembed=np.zeros((Aold.shape[0],d))
        for old,col in old_to_new.items():Aembed[:,col]=Aold.toarray()[:,old]
        base_rows=list(sg[:,None]*Aembed);groups={g:[j for j,(root,old) in enumerate(labels) if root==g] for g in range(qnext-1)}
        old_order={j:h0[old] for j,(root,old) in enumerate(labels) if old is not None}
        for initial,flip0,flip1 in it.product([-1,1],[False,True],[False,True]):
            phases=[];side=initial
            for g in range(qnext-2):
                if g:
                    if g in targetduplicates:
                        flip=flip0 if g==targetduplicates[0] else flip1
                        if flip:side=-side
                    else:side=-side
                phases.append(side)
            rows=base_rows.copy()
            for g,side in enumerate(phases):
                left=groups[g];right=groups[g+1]
                def extremes(indices):return sorted(indices,key=lambda j:old_order.get(j,0))
                left=extremes(left);right=extremes(right);l=left[-1] if side>0 else left[0];m=right[0] if side>0 else right[-1];a,b=roots[l],roots[m]
                for r in range(d):
                    if r in [l,m]:continue
                    coef=np.zeros(d);coef[l]=b-roots[r];coef[m]=roots[r]-a;coef[r]-=b-a
                    orientation=side*(1 if roots[r]<=a else -1);rows.append(coef*orientation)
            A=np.array(rows);sc=np.max(np.abs(A),axis=1);assert all(sc>1e-12);A/=sc[:,None];M=np.column_stack([-A,np.ones(len(A))]);objective=np.zeros(d+1);objective[-1]=-1
            with warnings.catch_warnings():
                warnings.simplefilter('ignore');lp=linprog(objective,A_ub=M,b_ub=np.zeros(len(M)),bounds=[(-1,1)]*d+[(0,1)],method='highs',options={'threads':1,'time_limit':30})
            margin=float(lp.x[-1]) if lp.success else None;record=dict(q=q,qnext=qnext,shifted_old_group=shifted,slot_shift=shift,target_duplicate_groups=targetduplicates,phases=phases,status=int(lp.status),margin=margin,passed=False)
            if margin and margin>1e-9:
                vv=[F(float(x+2)).limit_denominator(10**12) for x in lp.x[:-1]]
                # Generic perturbations preserve all strict constraints and
                # remove LP coincidences away from the prescribed axis cores.
                for pert in [F(0),F(str(margin))/10000,F(str(margin))/20000,F(str(margin))/40000]:
                    hs=[h+pert*i for i,h in enumerate(vv)];rr=[F(float(a)).limit_denominator(10**15) for a in roots];ll=[(F(0),F(1),F(0))]+[(F(1),-h,a) for h,a in zip(hs,rr)];r=ledger(ll)
                    if r is None:continue
                    old_ll=[ll[0]]+[ll[old_to_new[i]+1] for i in range(len(oldgroups))];prev=arrangement(old_ll);Tprev=len(prev['triangles']);full=arrangement(ll);axis_count=sum(0 in t for t in full['triangles'])
                    if Tprev!=raw['T'] or axis_count!=qnext-2:continue
                    record.update(passed=True,exact_ledger=r,old_subset_T=Tprev,axis_triangles=axis_count)
                    proposal=dict(record,n=qnext+2,q=qnext,T=r['T'],root_group_indices=[g for g,old in labels],duplicate_ranks=sorted(targetduplicates),reciprocal_slopes=list(map(str,hs)),lines_frac=[[str(v) for v in l] for l in ll],source=str(source.relative_to(ROOT)),retained_parent_indices=[0]+[old_to_new[i]+1 for i in range(len(oldgroups))],status_note='Exact rational adaptive-child point and parent-subset replay; actual tangent intervals and scalable shape/count theorem pending')
                    out=ROOT/'research/openmath-seven-hour-2026-10-05/seed_search'/args.tag;out.mkdir(parents=True,exist_ok=True);p=out/f'T{r["T"]}-shift{shifted}_{shift}-phase{initial}_{int(flip0)}_{int(flip1)}.json';p.write_text(json.dumps(proposal,indent=2)+'\n');record['proposal']=str(p.relative_to(ROOT));print(json.dumps(dict(event='candidate',**{k:record[k] for k in ['qnext','shifted_old_group','slot_shift','margin','exact_ledger','old_subset_T','axis_triangles']})),flush=True);break
            refinements.append(record)
    out=ROOT/'research/openmath-seven-hour-2026-10-05/seed_search'/args.tag;out.mkdir(parents=True,exist_ok=True);report=dict(source=str(source.relative_to(ROOT)),refinements=refinements,seconds=time.time()-start,scope='Bounded actual old-type-preserving adaptive root/grid refinement with prescribed child caps; no infinite recurrence inferred');(out/'report.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(dict(fits=sum(r['passed'] for r in refinements),tested=len(refinements),best=max((r['exact_ledger']['T'] for r in refinements if r['passed']),default=0),seconds=time.time()-start)),flush=True)

if __name__=='__main__':main()
