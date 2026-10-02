"""Tangent-grid LP fitting directly from attributed pseudoline words.

All projective recharting signs are derived from the rank-three chirotope;
no initial straight-line realization is presumed. Fixed tangent intercepts
make all remaining orientation inequalities linear in reciprocal slopes.
Numerical infeasibility has only diagnostic status. A feasible proposal must
pass exact rational counters and, separately, true-tangent interval checks.
"""
from pathlib import Path
import os
os.environ.setdefault('OMP_NUM_THREADS','1');os.environ.setdefault('OPENBLAS_NUM_THREADS','1')
import sys,json,time,itertools as it,math,argparse,hashlib,warnings,random
from fractions import Fraction as F
from functools import cmp_to_key
ROOT=Path(__file__).resolve().parents[2]
sys.path.insert(0,str(ROOT/'work/construction-deps'));sys.path.insert(0,str(ROOT/'research/kobon-hybrid'))
import numpy as np
from scipy.optimize import linprog
from exact_geometry import arrangement,primitive,read_lines
from verify_direct import verify


def tensor(n,entries):
    chi=np.zeros((n,n,n),dtype=np.int8)
    for (i,j,k),s in entries:
        for a,b,c in ((i,j,k),(j,k,i),(k,i,j)):chi[a,b,c]=s
        for a,b,c in ((j,i,k),(i,k,j),(k,j,i)):chi[a,b,c]=-s
    return chi


def from_word(raw):
    word=list(map(int,raw.split(')',1)[1].split()));n=max(word)+2
    assert len(word)==n*(n-1)//2
    perm=list(range(n));rows=[[]for _ in range(n)]
    for g in word:
        i,j=perm[g:g+2];assert i<j
        rows[i].append(j);rows[j].append(i);perm[g],perm[g+1]=j,i
    assert perm==list(range(n))[::-1]
    positions=[{j:q for q,j in enumerate(row)}for row in rows]
    entries=[((i,j,k),-1 if positions[i][j]<positions[i][k] else 1)for i,j,k in it.combinations(range(n),3)]
    entries += [((i,j,n),1)for i,j in it.combinations(range(n),2)]
    return n,tensor(n+1,entries)


def chart_signs(chi,I,J):
    N=len(chi);K=next(k for k in range(N)if k not in(I,J));d=int(chi[I,J,K])
    ids=[k for k in range(N)if k not in(I,J)];A={k:int(chi[k,I,J])for k in ids}
    def comparison(l,m):return -d*int(chi[l,m,I])*A[l]*A[m]
    ids.sort(key=cmp_to_key(comparison));q=len(ids)
    assert all(comparison(ids[i],ids[j])<0 for i,j in it.combinations(range(q),2))
    signs=[d*int(chi[l,m,J])*A[l]*A[m]for l,m in it.combinations(ids,2)]
    signs += [int(chi[l,m,k])*A[l]*A[m]*A[k]for l,m,k in it.combinations(ids,3)]
    return ids,np.array(signs,dtype=np.int8)


def validate_chart_formula():
    # Independently compare all projective charts against concrete rational
    # coordinate transformations of the retained nine-line witness.
    from importlib.util import spec_from_file_location,module_from_spec
    sys.path.insert(0,str(ROOT/'work/general-bounds-deps'));sys.path.insert(0,str(ROOT/'research/kobon-extension'))
    spec=spec_from_file_location('transfer',ROOT/'experiments/2026-09-21/general-bounds/projective_seed_transfer.py');mod=module_from_spec(spec);spec.loader.exec_module(mod)
    lines=read_lines(ROOT/'research/finite-table/classical-009.json');rows=[(a,b,-c)for a,b,c in lines]+[(0,0,1)];N=len(rows)
    entries=[]
    for i,j,k in it.combinations(range(N),3):
        det=mod.dot(rows[i],mod.cross(rows[j],rows[k]));assert det
        entries.append(((i,j,k),1 if det>0 else-1))
    chi=tensor(N,entries)
    for I,J in it.permutations(range(N),2):
        base,K=mod.normalize_projective(rows,I,J);ids,signs=chart_signs(chi,I,J)
        assert ids==[b[2]for b in base]
        aa=[b[0]for b in base];v=[b[1]for b in base]
        expected=[1 if v[i]>v[j]else-1 for i,j in it.combinations(range(N-2),2)]
        for i,j,k in it.combinations(range(N-2),3):
            det=(aa[j]-aa[k])*v[i]+(aa[k]-aa[i])*v[j]+(aa[i]-aa[j])*v[k]
            expected.append(1 if det>0 else-1)
        assert np.array_equal(signs,expected),(I,J)
    return dict(test='projective sign formula against exact rational coordinate transformations',charts=N*(N-1),passed=True)


def run(source,out,seconds,epsilon,seed,start_class,max_classes):
    source=source.resolve();out=out.resolve();out.mkdir(parents=True,exist_ok=True);start=time.time();rng=random.Random(seed)
    check=validate_chart_formula();print(json.dumps(check),flush=True)
    raw=[l for l in source.read_text().splitlines()if ')'in l]
    chosen=list(enumerate(raw))[start_class:start_class+max_classes if max_classes else None]
    report=dict(source=str(source.relative_to(ROOT)),source_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),
      input_attribution='Roman Parpalak and Denis Utkin; arXiv:2607.29236; pinned primary-inputs manifest',
      epsilon=epsilon,seed=seed,time_limit=seconds,chart_formula_check=check,classes_total=len(raw),records=[],wins=[])
    seen={};cache={};tested=0;duplicates=0;bestmargin=0.0
    for class_index,text in chosen:
        n,chi=from_word(text);q=n-1;label=text.split(')')[0].strip()
        if q not in cache:
            aa=np.array(sorted([math.tan(k*math.pi/q)for k in range(-q//2+1,q//2)if k]+[-epsilon,epsilon]))
            pairs=list(it.combinations(range(q),2));triples=list(it.combinations(range(q),3))
            rawmat=np.zeros((len(pairs)+len(triples),q+1))
            for r,(i,j)in enumerate(pairs):rawmat[r,i]=1;rawmat[r,j]=-1
            for r,(i,j,k)in enumerate(triples,len(pairs)):
                rawmat[r,i]=aa[j]-aa[k];rawmat[r,j]=aa[k]-aa[i];rawmat[r,k]=aa[i]-aa[j]
            rawmat/=np.max(abs(rawmat),axis=1)[:,None]
            cache[q]=(aa,rawmat)
        aa,rawmat=cache[q];obj=np.zeros(q+1);obj[-1]=-1
        charts=list(it.permutations(range(n+1),2));rng.shuffle(charts)
        for I,J in charts:
            if time.time()-start>seconds:break
            ids,sg=chart_signs(chi,I,J);key=sg.tobytes()
            if key in seen:duplicates+=1;continue
            seen[key]=(class_index,I,J);matrix=-sg[:,None]*rawmat;matrix[:,-1]=1
            with warnings.catch_warnings():
                warnings.simplefilter('ignore')
                result=linprog(obj,A_ub=matrix,b_ub=np.zeros(len(matrix)),bounds=[(-1,1)]*q+[(0,1)],method='highs',options={'threads':1,'time_limit':5})
            tested+=1;margin=float(result.x[-1])if result.success else None
            if margin is not None:bestmargin=max(bestmargin,margin)
            row=dict(class_index=class_index,label=label,I=I,J=J,margin=margin,status=int(result.status))
            report['records'].append(row)
            if margin is not None and margin>1e-8:
                vv=[F(float(v)).limit_denominator(10**9)for v in result.x[:-1]]
                if vv[q//2-1]<vv[q//2]:vv=[-v for v in vv]
                vv=[v+2 for v in vv]
                eps=F(1,10**7)if not epsilon else F(str(epsilon))
                intercepts=[F(float(a)).limit_denominator(10**12)for a in aa]
                intercepts[q//2-1]=-eps;intercepts[q//2]=eps
                lines=[(0,1,0)]+[primitive((1,-v,a))for a,v in zip(intercepts,vv)]
                ar=arrangement(lines);T=len(ar['triangles']);caps=sum(0 in t for t in ar['triangles'])
                path=out/f'n{n:03d}-class{class_index:04d}-I{I:02d}-J{J:02d}.json'
                data=dict(n=n,triangle_count=T,lines_frac=[[str(v)for v in l]for l in lines],
                  reciprocal_slopes=[str(v)for v in vv],epsilon=str(eps),Y0_triangles=caps,
                  source=str(source.relative_to(ROOT)),source_class=class_index,chart=[I,J],line_labels=ids,
                  numerical_lp_margin=margin,verification='Exact rational midpoint only; true-tangent interval verification pending',
                  attribution='Pseudoline type from Parpalak--Utkin; independently fitted reciprocal slopes')
                path.write_text(json.dumps(data,indent=2)+'\n');data['direct']=verify(path)
                report['wins'].append(str(path.relative_to(ROOT)));print(json.dumps(dict(event='feasible',n=n,T=T,caps=caps,**row)),flush=True)
            if tested%100==0:
                print(json.dumps(dict(event='progress',class_index=class_index,tested=tested,duplicates=duplicates,best_margin=bestmargin,wins=len(report['wins']),seconds=time.time()-start)),flush=True)
                report.update(tested=tested,duplicates=duplicates,best_margin=bestmargin,seconds=time.time()-start)
                (out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
        if time.time()-start>seconds:break
    report.update(tested=tested,duplicates=duplicates,best_margin=bestmargin,seconds=time.time()-start,
                  scope='Floating LP diagnostics over explicitly tested chart/type pairs; no proof of nonstretchability or of universal incompatibility.')
    (out/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(dict(event='done',tested=tested,duplicates=duplicates,best_margin=bestmargin,wins=report['wins'],seconds=time.time()-start)),flush=True)


if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('source',type=Path);p.add_argument('--out',type=Path,required=True)
    p.add_argument('--seconds',type=float,default=600);p.add_argument('--epsilon',type=float,default=0)
    p.add_argument('--seed',type=int,default=20261002);p.add_argument('--start-class',type=int,default=0);p.add_argument('--max-classes',type=int,default=0)
    a=p.parse_args();run(a.source,a.out,a.seconds,a.epsilon,a.seed,a.start_class,a.max_classes)
