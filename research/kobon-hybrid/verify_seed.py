"""Rigorous rational interval certificate for an 11-line, 32-triangle seed.

Standard library only. No floating-point arithmetic is used in this verifier.
The mathematical inputs are Machin's formula, Taylor's remainder bound, and
invariance of a simple affine arrangement when no determinant changes sign.
The infinite-family deduction separately invokes BBL Proposition 3.1.
"""
from fractions import Fraction as F
from math import factorial
from itertools import combinations
from pathlib import Path
import json
from exact_geometry import primitive,arrangement
from verify_direct import verify

SCALE=10**60
EPS=F(1,100000)
Q=10
V=[F(x,10) for x in [15,-2,14,1,4,-4,5,-3,12,-5]]


def down(x):return F(x.numerator*SCALE//x.denominator,SCALE)
def up(x):return -down(-x)


class I:
    def __init__(self,lo,hi=None):
        self.lo=F(lo);self.hi=F(lo if hi is None else hi)
        assert self.lo<=self.hi
    def __add__(self,other):
        if not isinstance(other,I):other=I(other)
        return I(down(self.lo+other.lo),up(self.hi+other.hi))
    __radd__=__add__
    def __neg__(self):return I(-self.hi,-self.lo)
    def __sub__(self,other):return self+(-other if isinstance(other,I) else -F(other))
    def __mul__(self,other):
        if not isinstance(other,I):other=I(other)
        vals=[a*b for a in (self.lo,self.hi) for b in (other.lo,other.hi)]
        return I(down(min(vals)),up(max(vals)))
    __rmul__=__mul__
    def __truediv__(self,other):
        if not isinstance(other,I):other=I(other)
        assert not other.lo<=0<=other.hi
        vals=[1/other.lo,1/other.hi]
        return self*I(min(vals),max(vals))
    def midpoint(self):return (self.lo+self.hi)/2
    def sign(self):return 1 if self.lo>0 else -1 if self.hi<0 else 0


def atan_inverse(d,terms=80):
    # Consecutive partial sums of an alternating series bracket its limit.
    s=sum((F(1 if k%2==0 else -1,(2*k+1)*d**(2*k+1)) for k in range(terms)),F(0))
    next_term=F(1 if terms%2==0 else -1,(2*terms+1)*d**(2*terms+1))
    return I(min(s,s+next_term),max(s,s+next_term))


PI=16*atan_inverse(5)-4*atan_inverse(239)
assert F(3141592653589793238,10**18)<PI.lo<PI.hi<F(3141592653589793239,10**18)


def sin_cos(x,terms=50):
    x2=x*x
    s=I(F((-1)**terms,factorial(2*terms+1)))
    c=I(F((-1)**terms,factorial(2*terms)))
    for k in range(terms-1,-1,-1):
        s=s*x2+F((-1)**k,factorial(2*k+1))
        c=c*x2+F((-1)**k,factorial(2*k))
    s=s*x
    bound=max(abs(x.lo),abs(x.hi))
    es=bound**(2*terms+2)/factorial(2*terms+2)
    ec=bound**(2*terms+1)/factorial(2*terms+1)
    return s+I(-es,es),c+I(-ec,ec)


def tan_pi(k,q):
    assert 0<2*k<q
    s,c=sin_cos(PI*F(k,q))
    assert c.lo>0
    return s/c


def grid(epsilon):
    positive=[tan_pi(k,Q) for k in range(1,Q//2)]
    return [-x for x in positive[::-1]]+[I(-epsilon),I(epsilon)]+positive


def verify_seed(output_dir=None):
    dest=Path(output_dir) if output_dir else Path(__file__).parent
    dest.mkdir(parents=True,exist_ok=True)
    at0,at1=grid(F(0)),grid(EPS)
    assert len(set(V))==Q and all(V)
    assert V[Q//2-1]>0>V[Q//2]
    minimum=F(100)
    for i,j,k in combinations(range(Q),3):
        signs=[]
        for a in (at0,at1):
            d=(a[j]-a[k])*V[i]+(a[k]-a[i])*V[j]+(a[i]-a[j])*V[k]
            assert d.sign(),('Unresolved determinant',i,j,k,d.lo,d.hi)
            signs.append(d.sign());minimum=min(minimum,abs(d.lo),abs(d.hi))
        assert signs[0]==signs[1],('Sign changes before epsilon reaches zero',i,j,k)
    # Determinants are affine in epsilon, so equal strict signs at the endpoints
    # establish the same sign throughout [0,EPS]. Intersections with Y0 have
    # strictly ordered intercepts for every 0<epsilon<=EPS; epsilon=0 itself is
    # deliberately not claimed to define a simple arrangement.
    aa=[a.midpoint() for a in at1]
    assert all(a<b for a,b in zip(aa,aa[1:]))
    lines=[(0,1,0)]+[primitive((1,-v,a)) for a,v in zip(aa,V)]
    ar=arrangement(lines)
    assert len(ar['points'])==55 and all(len(s)==2 for s in ar['points'].values())
    assert len(ar['triangles'])==32
    assert sum(0 in tri for tri in ar['triangles'])==9
    certificate=dict(n=11,triangle_count=32,lines_frac=[[str(x) for x in l] for l in lines],
                     declared_parallel_pairs=[],
                     construction='Rational midpoint witness for the certified tangent-grid seed',
                     epsilon=str(EPS),reciprocal_slopes=[str(v) for v in V])
    path=dest/'seed-11-rational.json';path.write_text(json.dumps(certificate,indent=2))
    independent=verify(path)
    orders=[[next(j for j in ar['points'][p] if j!=i) for p in row]
            for i,row in enumerate(ar['rows'])]
    combinatorics=dict(line_numbering='0 is Y0; 1 through 10 follow the coefficient table',
                       crossing_orders=orders,triangles=sorted(ar['triangles']),
                       triangles_touching_Y0=sorted(tri for tri in ar['triangles'] if 0 in tri))
    (dest/'seed-combinatorics.json').write_text(json.dumps(combinatorics,indent=2))
    report=dict(seed_lines=11,triangles=32,triangles_touching_Y0=9,simple=True,
                epsilon_interval='0 < epsilon <= 1/100000',
                non_Y_triples=120,endpoint_interval_checks=240,
                constant_nonparallel_pairs=45,determinant_margin_lower_bound=str(minimum),
                safe_readable_margin='> 0.034',
                trigonometry='Machin formula and Taylor remainders, rational intervals, outward rounding',
                independent_reference_check=independent,
                family_N='10*2^t+1',family_T='(100*4^t-4)/3 = N*(N-2)/3-1',
                family_scope='Computer-assisted seed proof plus published BBL Proposition 3.1 and Remark 3.2; not Lean formalization')
    assert minimum>F(34,1000)
    (dest/'seed-verification.json').write_text(json.dumps(report,indent=2))
    print('PASS: 32 triangles, all 9 bounded Y0 segments used, 240 rigorous interval sign checks.')
    print('PASS: the seed type persists for every 0 < epsilon <= 1/100000.')
    return report


if __name__=='__main__':verify_seed()
