"""Transfer an optimal21 oriented matroid to the exact BBL tangent grid.

All determinant inequalities are linear in reciprocal slopes V once the
intercepts are fixed. Floating LP solutions are proposals, never certificates.
Every feasible candidate is checked by two exact rational triangle counters.
"""
from pathlib import Path
from fractions import Fraction as F
from itertools import combinations
import json,sys,time
import numpy as np

ROOT=Path(__file__).resolve().parents[3]
sys.path.insert(0,str(ROOT/'work/general-bounds-deps'))
from scipy.optimize import linprog
sys.path.insert(0,str(ROOT/'research/kobon-hybrid'))
from exact_geometry import arrangement,primitive,read_lines
from verify_seed import tan_pi
from verify_direct import verify
OUT=Path(__file__).parent/'lp-compatible21';OUT.mkdir(exist_ok=True)


def coefficients(a):
    rows=[]
    for i,j,k in combinations(range(20),3):
        row=np.zeros(20);row[i]=a[k]-a[j];row[j]=a[i]-a[k];row[k]=a[j]-a[i]
        rows.append(row)
    for i,j in combinations(range(20),2):
        row=np.zeros(20);row[i]=1;row[j]=-1;rows.append(row)
    return np.array(rows)


def transformed(lines,i,j):
    # Rows prescribe new primal coordinates X, Y=L_i, Z=L_j.
    bases=[np.array([e,lines[i],lines[j]]) for e in np.eye(3)]
    T=max(bases,key=lambda t:abs(np.linalg.det(t)))
    new=lines@np.linalg.inv(T)
    labels=[k for k in range(len(lines)) if k not in (i,j)]
    A=-new[labels,2]/new[labels,0]
    V=-new[labels,1]/new[labels,0]
    order=np.argsort(A)
    return A[order],V[order],[labels[k] for k in order]


def validate(v,aa,tag,details):
    vals=[F(float(x)).limit_denominator(10**12) for x in v]
    # A shear gives opposite central signs while preserving the arrangement.
    center=(vals[9]+vals[10])/2
    vals=[x-center for x in vals]
    if vals[9]<vals[10]:vals=[-x for x in vals]
    lines=[(0,1,0)]+[primitive((1,-x,a)) for x,a in zip(vals,aa)]
    ar=arrangement(lines)
    T=len(ar['triangles']);C=sum(0 in t for t in ar['triangles'])
    out=dict(details,triangles=T,caps=C,simple=len(ar['points'])==210,
             V=[str(v) for v in vals])
    if T>=133 and C==19 and out['simple']:
        path=OUT/f'candidate-{tag}.json'
        data=dict(n=21,triangle_count=T,lines_frac=[[str(x) for x in l] for l in lines],
                  construction='LP transfer of optimal21 oriented matroid to BBL tangent grid',
                  priority_status='Unestablished',provenance=details)
        path.write_text(json.dumps(data,indent=2)+'\n')
        out['direct']=verify(path);out['path']=str(path.relative_to(ROOT))
    return out


def main():
    start=time.monotonic()
    orig=read_lines(ROOT/'research/finite-table/simple-021.json')
    lines=np.array([[float(a),float(b),-float(c)] for a,b,c in orig]+[[0.,0.,1.]])
    lines=lines/np.linalg.norm(lines,axis=1)[:,None]
    allcharts=[]
    for i in range(22):
        for j in range(22):
            if i==j:continue
            a,v,labels=transformed(lines,i,j)
            signs=np.sign(coefficients(a)@v)
            assert not np.any(signs==0)
            allcharts.append((i,j,signs,labels))
    logs=[];found=[]
    for eps in [F(0),F(1,1000),F(1,10000),F(1,100000),F(1,1000000),F(1,100),F(1,10**8)]:
        aa=[-tan_pi(k,20).midpoint() for k in range(9,0,-1)]+[-eps,eps]+[tan_pi(k,20).midpoint() for k in range(1,10)]
        a=np.array(list(map(float,aa)));coeff=coefficients(a)
        coeff=coeff/np.max(abs(coeff),axis=1)[:,None]
        for i,j,signs,labels in allcharts:
            mat=np.column_stack((-coeff*signs[:,None],np.ones(len(coeff))))
            objective=np.zeros(21);objective[-1]=-1
            sol=linprog(objective,A_ub=mat,b_ub=np.zeros(len(mat)),
                        bounds=[(-1,1)]*20+[(0,None)],method='highs',
                        options={'dual_feasibility_tolerance':1e-9,'primal_feasibility_tolerance':1e-9})
            margin=float(sol.x[-1]) if sol.success else 0.
            record=dict(Y0=i,infinity=j,epsilon=str(eps),status=int(sol.status),margin=margin)
            logs.append(record)
            if margin>1e-8:
                details=dict(record,source='research/finite-table/simple-021.json',labels=labels)
                actual_aa=aa if eps else aa[:9]+[-F(1,100000),F(1,100000)]+aa[11:]
                result=validate(sol.x[:-1],actual_aa,len(logs),details);found.append(result)
                print('CANDIDATE',json.dumps(result),flush=True)
                (OUT/'candidates.json').write_text(json.dumps(found,indent=2)+'\n')
                if result['triangles']>=133 and result['caps']==19 and result['simple']:
                    (OUT/'report.json').write_text(json.dumps(dict(success=True,checks=logs,candidates=found,seconds=time.monotonic()-start),indent=2)+'\n')
                    return
        print('EPS COMPLETE',str(eps),'best margin',max(x['margin'] for x in logs),'checks',len(logs),flush=True)
        (OUT/'progress.json').write_text(json.dumps(dict(checks=logs,candidates=found,seconds=time.monotonic()-start),indent=2)+'\n')
    (OUT/'report.json').write_text(json.dumps(dict(success=False,checks=logs,candidates=found,seconds=time.monotonic()-start),indent=2)+'\n')

if __name__=='__main__':main()
