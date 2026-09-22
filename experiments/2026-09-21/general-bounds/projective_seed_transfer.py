"""Fit augmented perfect projective arrangements to a BBL tangent grid.

Append the original line at infinity, select a new distinguished line I and
line at infinity J, and preserve the resulting affine chirotope using an LP
linear in reciprocal slopes. Strict feasibility is only a proposal until exact
coordinate and trigonometric-interval certification succeeds.
"""
import argparse,itertools,json,math,sys,time
from fractions import Fraction as F
from pathlib import Path
import numpy as np
ROOT=Path(__file__).resolve().parents[3]
sys.path.insert(0,str(ROOT/'work/general-bounds-deps'))
sys.path.insert(0,str(ROOT/'research/kobon-extension'))
from scipy.optimize import linprog
from exact_geometry import read_lines,arrangement,primitive

def cross(u,v):return (u[1]*v[2]-u[2]*v[1],u[2]*v[0]-u[0]*v[2],u[0]*v[1]-u[1]*v[0])
def dot(u,v):return sum(a*b for a,b in zip(u,v))

def normalize_projective(rows,I,J):
    c0=cross(rows[I],rows[J])
    K=next(k for k,H in enumerate(rows)if dot(H,c0))
    c1=cross(rows[J],rows[K]);c2=cross(rows[K],rows[I])
    base=[]
    for k,H in enumerate(rows):
        if k in (I,J):continue
        A=dot(H,c0);B=dot(H,c1);C=dot(H,c2)
        assert A
        base.append((F(-C,A),F(-B,A),k))
    return sorted(base),K

def fit(path,out,epsilon=0.0):
    out.mkdir(parents=True,exist_ok=True)
    source=read_lines(path);n=len(source);q=n-1
    rows=[(a,b,-c)for a,b,c in source]+[(0,0,1)]
    triples=list(itertools.combinations(range(q),3));pairs=list(itertools.combinations(range(q),2))
    aa=np.array(sorted([math.tan(k*math.pi/q)for k in range(-q//2+1,q//2)if k]+[-epsilon,epsilon]))
    raw=np.zeros((len(pairs)+len(triples),q+1))
    for r,(i,j)in enumerate(pairs):raw[r,i]=1;raw[r,j]=-1
    for r,(i,j,k)in enumerate(triples,start=len(pairs)):
        raw[r,i]=aa[j]-aa[k];raw[r,j]=aa[k]-aa[i];raw[r,k]=aa[i]-aa[j]
    raw/=np.max(np.abs(raw),axis=1)[:,None]
    obj=np.zeros(q+1);obj[-1]=-1;seen={};reports=[];start=time.monotonic();wins=[]
    for I,J in itertools.permutations(range(n+1),2):
        base,K=normalize_projective(rows,I,J);a=[b[0]for b in base];v=[b[1]for b in base]
        sg=[]
        for i,j in pairs:sg.append(1 if v[i]>v[j]else-1)
        for i,j,k in triples:
            d=(a[j]-a[k])*v[i]+(a[k]-a[i])*v[j]+(a[i]-a[j])*v[k]
            assert d
            sg.append(1 if d>0 else-1)
        key=bytes(s+1 for s in sg)
        if key in seen:
            reports.append(dict(I=I,J=J,duplicate_of=seen[key]));continue
        seen[key]=(I,J);mat=-np.array(sg)[:,None]*raw;mat[:,-1]=1
        result=linprog(obj,A_ub=mat,b_ub=np.zeros(len(mat)),bounds=[(-1,1)]*q+[(0,1)],method='highs')
        margin=float(result.x[-1])if result.success else None
        reports.append(dict(I=I,J=J,K=K,margin=margin,status=result.message))
        if margin is not None and margin>1e-8:
            vv=[F(float(z)).limit_denominator(10**7)for z in result.x[:-1]]
            eps=F(1,10**6)if epsilon==0 else F(str(epsilon))
            aaa=[F(float(z)).limit_denominator(10**10)for z in aa]
            aaa[q//2-1]=-eps;aaa[q//2]=eps
            ls=[(0,1,0)]+[primitive((1,-z,x))for z,x in zip(vv,aaa)]
            ar=arrangement(ls);T=len(ar['triangles']);caps=sum(0 in t for t in ar['triangles'])
            win=dict(n=n,triangle_count=T,source=str(path.relative_to(ROOT)),I=I,J=J,K=K,
                     epsilon=str(eps),lp_epsilon=epsilon,margin=margin,Y0_triangles=caps,
                     reciprocal_slopes=[str(z)for z in vv],lines_frac=[[str(z)for z in l]for l in ls],
                     verification='Exact rational midpoint count; actual tangent-grid interval proof pending')
            dest=out/f'n{n:03d}-I{I:02d}-J{J:02d}.json';dest.write_text(json.dumps(win,indent=2)+'\n')
            wins.append(str(dest));print(json.dumps({k:win[k]for k in ('n','I','J','margin','triangle_count','Y0_triangles')}),flush=True)
        if len(reports)%25==0:print(json.dumps(dict(n=n,pairs=len(reports),unique=len(seen),wins=len(wins),seconds=time.monotonic()-start)),flush=True)
    summary=dict(source=str(path.relative_to(ROOT)),n=n,epsilon=epsilon,pairs=len(reports),unique=len(seen),
                 seconds=time.monotonic()-start,wins=wins,results=reports,
                 limitations='Floating LP proposals and infeasibility reports; exact finite checks only for saved feasible witnesses. No infeasibility proof.')
    (out/f'report-{n:03d}-eps{epsilon}.json').write_text(json.dumps(summary,indent=2)+'\n')
    print(json.dumps({k:summary[k]for k in ('n','pairs','unique','seconds','wins')}),flush=True)

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('source',type=Path);p.add_argument('--out',type=Path,required=True);p.add_argument('--epsilon',type=float,default=0)
    a=p.parse_args();fit(a.source.resolve(),a.out,a.epsilon)
