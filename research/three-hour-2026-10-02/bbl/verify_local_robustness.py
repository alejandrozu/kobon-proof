"""Exact outward-rounded interval audit of a local ten-sign obstruction.

Only Python's standard library is used. Every arithmetic operation rounds
outward to a fixed dyadic grid. Gaussian elimination solves nine coefficient
equations with the tenth Farkas weight fixed to one. The remaining two
equations follow from the always-zero sums of coefficients and a-weighted
coefficients. This is exact computer-assisted evidence, not a Lean theorem.
"""
from pathlib import Path
from fractions import Fraction as F
import json,time,hashlib
ROOT=Path(__file__).resolve().parents[3]
SOURCE=ROOT/'research/three-hour-2026-10-02/constructions/grid21-obstruction/representative-238.json'
PRECISION=120
SCALE=1<<PRECISION

def rounded(lo,hi):
    return F(lo.numerator*SCALE//lo.denominator,SCALE),F(-((-hi.numerator*SCALE)//hi.denominator),SCALE)
class I:
    def __init__(self,a,b=None):self.lo,self.hi=rounded(F(a),F(a if b is None else b))
    def __add__(self,o):
        o=box(o);return I(self.lo+o.lo,self.hi+o.hi)
    __radd__=__add__
    def __neg__(self):return I(-self.hi,-self.lo)
    def __sub__(self,o):return self+-box(o)
    def __rsub__(self,o):return box(o)+-self
    def __mul__(self,o):
        o=box(o);p=[x*y for x in(self.lo,self.hi)for y in(o.lo,o.hi)];return I(min(p),max(p))
    __rmul__=__mul__
    def __truediv__(self,o):
        o=box(o)
        if o.lo<=0<=o.hi:raise ZeroDivisionError('interval contains zero')
        return self*I(1/o.hi,1/o.lo)
    def mid(self):return (self.lo+self.hi)/2
    def record(self):return {'lower':str(self.lo),'upper':str(self.hi),'approx':[float(self.lo),float(self.hi)]}
def box(v):return v if isinstance(v,I)else I(v)
def poly(cs,t):
    z=I(0)
    for c in cs:z=z*t+F(c)
    return z
def solve(A,b):
    n=len(b);M=[list(row)+[rhs]for row,rhs in zip(A,b)];pivots=[];swaps=[]
    for k in range(n):
        pivot=max(range(k,n),key=lambda j:abs(M[j][k].mid()))
        swaps.append(pivot);M[k],M[pivot]=M[pivot],M[k]
        p=M[k][k]
        if p.lo<=0<=p.hi:raise ZeroDivisionError('uncertain pivot')
        pivots.append(p)
        for i in range(k+1,n):
            f=M[i][k]/p
            for j in range(k+1,n+1):M[i][j]=M[i][j]-f*M[k][j]
            M[i][k]=I(0) # exact elimination identity, not interval subtraction
    x=[I(0)for _ in range(n)]
    for k in reversed(range(n)):
        x[k]=(M[k][n]-sum((M[k][j]*x[j]for j in range(k+1,n)),I(0)))/M[k][k]
    return x,pivots,swaps
def check(delta,data):
    lo=F(158384440324536293838883092694,10**30)
    hi=F(158384440324536293838883092695,10**30)
    quartic=lambda z:z**4-4*z**3-14*z**2-4*z+1
    assert F(3,20)<lo<hi<F(17,100)
    assert quartic(lo)>0>quartic(hi)
    t=I(lo,hi)
    ts=[poly(data['tangent_coefficients'][str(k)],t)for k in range(10)]
    a=[-ts[k]for k in range(9,0,-1)]+[I(0),I(0)]+[ts[k]for k in range(1,10)]
    a=[z+I(-delta,delta)for z in a]
    used=sorted({j for _,i,j,k,_ in data['support']for j in(i,j,k)})
    omitted=[used[0],used[-1]];cols=[j for j in used if j not in omitted]
    assert len(used)==11 and len(cols)==9
    rows=[]
    for _,i,j,k,sg in data['support']:
        row=[I(0)for _ in range(20)]
        row[i]=sg*(a[j]-a[k]);row[j]=sg*(a[k]-a[i]);row[k]=sg*(a[i]-a[j]);rows.append(row)
    B=[[rows[i][j]for i in range(9)]for j in cols]
    rhs=[-rows[9][j]for j in cols]
    try:x,pivots,swaps=solve(B,rhs)
    except ZeroDivisionError as exc:return {'delta':str(delta),'passed':False,'reason':str(exc)}
    passed=all(z.lo>0 for z in x)and a[omitted[0]].hi<a[omitted[1]].lo
    return {'delta':str(delta),'passed':passed,'used_intercepts':used,'omitted_columns':omitted,
      'solved_columns':cols,'intercept_boxes':{str(j):a[j].record()for j in used},
      'pivot_swaps':swaps,'pivots':[z.record()for z in pivots],
      'weights':[z.record()for z in x]+[I(1).record()]}
def main():
    import argparse
    parser=argparse.ArgumentParser()
    parser.add_argument('--out',type=Path,default=Path(__file__).with_name('local-robustness.json'))
    args=parser.parse_args()
    start=time.time();data=json.loads(SOURCE.read_text(encoding='utf-8'))
    trials=[]
    for k in range(1,13):
        result=check(F(1,10**k),data);trials.append({'delta':result['delta'],'passed':result['passed']})
        if result['passed']:break
    assert result['passed']
    result.update({'scope':'Exact interval proof for one explicit ten-sign system under independent noncentral intercept perturbations; no classification or global upper-bound claim.',
      'lean_status':'The exact-center obstruction is in Lean; this local robustness interval audit is not formalized in Lean.',
      'dyadic_rounding_bits':PRECISION,'source_sha256':hashlib.sha256(SOURCE.read_bytes()).hexdigest(),
      'trials':trials,'seconds':time.time()-start})
    target=args.out;target.parent.mkdir(parents=True,exist_ok=True)
    target.write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(json.dumps({'passed':True,'delta':result['delta'],'minimum_weight_lower':min(float(F(z['lower']))for z in result['weights']),
      'seconds':result['seconds'],'artifact':str(target)}))
if __name__=='__main__':main()
