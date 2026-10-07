"""Try the explicit regular-axis singular-grid corridor seed model.

There are q-1 roots tan(k*pi/q), including0, and two roots each support two
old lines. The axis then has two triple cores. All remaining pair/triple signs
are exact source data; LP trigonometry is a proposal only.
"""
from pathlib import Path
from fractions import Fraction as F
import itertools as it,json,sys,time,math,hashlib
ROOT=Path(__file__).resolve().parents[3]
sys.path.insert(0,str(ROOT/'experiments/2026-10-02'));sys.path.insert(0,str(Path(__file__).resolve().parent));sys.path.insert(0,str(ROOT/'research/kobon-hybrid'))
from word_grid_fit import tensor
from facet_walk61 import np,matrix,solve
from fit_optimal31_projective_charts import normalize,dot,cross
from exact_geometry import arrangement

if __name__=='__main__':
    start=time.time();sources=[(n,ROOT/f'research/six-hour-2026-09-21/general-bounds/parpalak-utkin-current/certificate-{n:03d}.json') for n in [8,26,50]]+[(50,ROOT/'work/openmath-rohith/kobon-triangles/submissions/n50/solution.json')]+[(14,ROOT/f'research/six-hour-2026-09-21/general-bounds/maiorana14/certificate-{i:02d}.json') for i in range(1,16) if i!=11];records=[]
    out=ROOT/'research/openmath-seven-hour-2026-10-05/seed_search/singular-corridor-grid';out.mkdir(parents=True,exist_ok=True)
    for n,source in sources:
        raw=json.loads(source.read_text());ll=[tuple(map(F,l)) for l in raw['lines_frac']] if 'lines_frac' in raw else [(F(a),F(b),-F(c)) for a,b,c in raw['lines']];ar=arrangement(ll);cores=[p for p,s in ar['points'].items() if len(s)>=3];common=set.intersection(*(set(ar['points'][p]) for p in cores));axis=next(iter(common));q=n-2
        assert len(cores)==2 and all(len(ar['points'][p])==3 for p in cores)
        hs=[(a,b,-c) for a,b,c in ll]+[(F(0),F(0),F(1))];entries=[]
        for i,j,k in it.combinations(range(n+1),3):
            value=dot(hs[i],cross(hs[j],hs[k]));entries.append(((i,j,k),(value>0)-(value<0)))
        chi=tensor(n+1,entries);base=normalize(hs,axis,n);ids=[label for a,h,label in base];group_roots=sorted(set(a for a,h,label in base));assert len(group_roots)==q-1
        regular=[math.tan(math.pi*k/q) for k in range(-q//2+1,q//2)];target={a:regular[r] for r,a in enumerate(group_roots)};roots=np.array([target[a] for a,h,label in base]);A,_,_=matrix(roots)
        K=next(k for k in range(n+1) if k not in [axis,n]);d=int(chi[axis,n,K]);am={k:int(chi[k,axis,n]) for k in ids}
        signs=[d*int(chi[l,m,n])*am[l]*am[m] for l,m in it.combinations(ids,2)]+[int(chi[l,m,k])*am[l]*am[m]*am[k] for l,m,k in it.combinations(ids,3)];signs=np.array(signs,dtype=np.int8);assert all(signs)
        candidate,status=solve(A,signs,30);record=dict(n=n,q=q,T=len(ar['triangles']),axis=axis,source=str(source.relative_to(ROOT)),source_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),duplicate_ranks=[r for r,a in enumerate(group_roots) if sum(x==a for x,h,l in base)>1],passed=candidate is not None,status=status)
        if candidate is not None:
            vv=[F(float(v+2)).limit_denominator(10**12) for v in candidate];rr=[F(float(x)).limit_denominator(10**15) for x in roots];lines=[(F(0),F(1),F(0))]+[(F(1),-h,a) for h,a in zip(vv,rr)];test=arrangement(lines);count=len(test['triangles']);axes_count=sum(0 in t for t in test['triangles']);record.update(exact_midpoint_T=count,axis_triangles=axes_count)
            p=out/f'n{n:03d}-source{source.parent.name}-{source.stem}-proposal.json';p.write_text(json.dumps(dict(record,source_labels=ids,root_group_indices=[group_roots.index(a) for a,h,l in base],reciprocal_slopes=list(map(str,vv)),lines_frac=[[str(v) for v in l] for l in lines],status_note='Floating positive-margin grid fit and exact rational midpoint. Actual tangent constants and geometric doubling/count invariant not yet proved'),indent=2)+'\n');record['proposal']=str(p.relative_to(ROOT))
        records.append(record);print(json.dumps(record),flush=True)
    (out/'report.json').write_text(json.dumps(dict(records=records,seconds=time.time()-start,scope='Bounded singular-grid fit of actual point types, no infinite-family claim'),indent=2)+'\n')
