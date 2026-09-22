"""Mixed-integer tangent-grid transfer preserving complete triangular faces.

Fixed reciprocal-slope order makes every triangle's same-side conditions a
set of linear triple-sign constraints. All distinguished-line caps are hard;
binary variables select which other source triangles must survive. Additional
new triangles are counted after solving. Every saved candidate is rationalized
and exactly recounted; solver upper bounds are exploratory, not formal proofs.
"""
import argparse,itertools,json,math,sys,time
from fractions import Fraction as F
from pathlib import Path
import numpy as np
from projective_seed_transfer import ROOT,normalize_projective
from scipy.optimize import milp,Bounds,LinearConstraint
from scipy.sparse import coo_matrix
from exact_geometry import read_lines,arrangement,primitive

def run(path,I,J,seconds,out,margin=1e-4):
    out.mkdir(parents=True,exist_ok=True);src=read_lines(path);n=len(src);q=n-1
    rows=[(a,b,-c)for a,b,c in src]+[(0,0,1)]
    base,K=normalize_projective(rows,I,J);a=[x[0]for x in base];v=[x[1]for x in base]
    sourceLines=[(0,1,0)]+[primitive((1,-vv,aa))for aa,vv,_ in base]
    sar=arrangement(sourceLines);sourceT=len(sar['triangles'])
    cap=[t for t in sar['triangles']if 0 in t];inside=[t for t in sar['triangles']if 0 not in t]
    assert len(cap)==q-1,(I,J,sourceT,len(cap))
    triples=list(itertools.combinations(range(q),3));ix={t:i for i,t in enumerate(triples)}
    aa=np.array(sorted([math.tan(k*math.pi/q)for k in range(-q//2+1,q//2)if k]+[0,0]))
    coeff=[]
    for i,j,k in triples:
        d=(a[j]-a[k])*v[i]+(a[k]-a[i])*v[j]+(a[i]-a[j])*v[k];assert d
        row={i:aa[j]-aa[k],j:aa[k]-aa[i],k:aa[i]-aa[j]}
        z=max(abs(x)for x in row.values());sg=1 if d>0 else-1
        coeff.append({i:sg*x/z for i,x in row.items()})
    def needed(t):
        old=[i-1 for i in t if i]
        req=set()
        for pair in itertools.combinations(old,2):
            for r in range(q):
                if r not in pair:req.add(ix[tuple(sorted((*pair,r)))])
        return req
    hard=set().union(*(needed(t)for t in cap));requirements=[needed(t)for t in inside]
    rr=[];cc=[];vv=[];lower=[];upper=[]
    def add(row,lo,hi=np.inf):
        r=len(lower);lower.append(lo);upper.append(hi)
        for c,val in row.items():rr.append(r);cc.append(c);vv.append(val)
    for i,j in itertools.combinations(range(q),2):
        sg=1 if v[i]>v[j]else-1;add({i:sg,j:-sg},margin)
    for r in hard:add(coeff[r],margin)
    bigM=2+margin
    for t,req in enumerate(requirements):
        for r in req-hard:
            row=coeff[r].copy();row[q+t]=-bigM;add(row,margin-bigM)
    nv=q+len(inside);mat=coo_matrix((vv,(rr,cc)),shape=(len(lower),nv)).tocsc()
    objective=np.concatenate((np.zeros(q),-np.ones(len(inside))))
    integ=np.concatenate((np.zeros(q),np.ones(len(inside))))
    bounds=Bounds(np.concatenate((-np.ones(q),np.zeros(len(inside)))),np.ones(nv))
    start=time.monotonic();print(json.dumps(dict(event='start',n=n,I=I,J=J,sourceT=sourceT,variables=nv,constraints=len(lower),hard_signs=len(hard))),flush=True)
    result=milp(objective,integrality=integ,bounds=bounds,constraints=LinearConstraint(mat,lower,upper),
                options=dict(time_limit=seconds,mip_rel_gap=0,presolve=True))
    report=dict(n=n,I=I,J=J,K=K,sourceT=sourceT,source_caps=len(cap),seconds=time.monotonic()-start,
        status=int(result.status),message=result.message,margin=margin,
        mip_gap=float(result.mip_gap)if getattr(result,'mip_gap',None)is not None else None,
        preserved_upper=float(-result.mip_dual_bound+len(cap))if getattr(result,'mip_dual_bound',None)is not None else None,
        limitations='Bounded floating MILP; no infeasibility/optimality proof for real arrangements; exact finite counts only.')
    if result.x is not None:
        slopes=[F(float(x)).limit_denominator(10**10)for x in result.x[:q]]
        points=[F(float(x)).limit_denominator(10**12)for x in aa]
        points[q//2-1]=F(-1,10**7);points[q//2]=F(1,10**7)
        ls=[(0,1,0)]+[primitive((1,-z,x))for x,z in zip(points,slopes)]
        ar=arrangement(ls);T=len(ar['triangles']);caps=sum(0 in t for t in ar['triangles'])
        report.update(exact_triangles=T,exact_caps=caps,preserved_selected=int(sum(result.x[q:]>.5))+len(cap),
                      simple=all(len(s)==2 for s in ar['points'].values()))
        cert=dict(n=n,triangle_count=T,source=f'Face-preservation MILP from {path.relative_to(ROOT)}',
                  lines_frac=[[str(x)for x in l]for l in ls],reciprocal_slopes=[str(x)for x in slopes],
                  epsilon='1/10000000',I=I,J=J,verification='Exact adjacency; interval tangent persistence pending')
        (out/f'n{n:03d}-I{I:02d}-J{J:02d}.json').write_text(json.dumps(cert,indent=2)+'\n')
    (out/f'n{n:03d}-I{I:02d}-J{J:02d}-report.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report),flush=True)

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('source',type=Path);p.add_argument('--I',type=int,default=0);p.add_argument('--J',type=int,required=True)
    p.add_argument('--seconds',type=float,default=180);p.add_argument('--out',type=Path,required=True);p.add_argument('--margin',type=float,default=1e-4)
    a=p.parse_args();run(a.source.resolve(),a.I,a.J,a.seconds,a.out,a.margin)
