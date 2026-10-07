"""Independent exact Q(sqrt(2)) geometry for the 8-line shared-edge counterexample.

No trigonometric chirotope formula is used in this check.  The field sign
test reduces to integer/rational square comparisons.  Output provides every
vertex, triangle, and shared side for a later direct Lean proof.
"""
from pathlib import Path
from fractions import Fraction as F
from dataclasses import dataclass
from collections import Counter, defaultdict
import itertools as it, json

ROOT=Path(__file__).resolve().parents[3]


@dataclass(frozen=True)
class S2:
    p:F=F(0)
    q:F=F(0)
    def __add__(self,y):
        if not isinstance(y,S2):y=S2(F(y))
        return S2(self.p+y.p,self.q+y.q)
    __radd__=__add__
    def __neg__(self):return S2(-self.p,-self.q)
    def __sub__(self,y):return self+-y
    def __mul__(self,y):
        if not isinstance(y,S2):y=S2(F(y))
        return S2(self.p*y.p+2*self.q*y.q,self.p*y.q+self.q*y.p)
    __rmul__=__mul__
    def __truediv__(self,y):
        if not isinstance(y,S2):y=S2(F(y))
        d=y.p*y.p-2*y.q*y.q
        assert d!=0
        return self*S2(y.p/d,-y.q/d)
    def sign(self):
        if not self.q:return (self.p>0)-(self.p<0)
        if not self.p:return (self.q>0)-(self.q<0)
        if self.p>0 and self.q>0:return 1
        if self.p<0 and self.q<0:return -1
        # sqrt(2) is irrational; equality here is impossible with p*q != 0.
        d=self.p*self.p-2*self.q*self.q
        assert d!=0
        return ((d>0)-(d<0))*(1 if self.p>0 else -1)
    def encoded(self):return [str(self.p),str(self.q)]


def meet(l,m):
    a,b,c=l;d,e,f=m
    determinant=a*e-b*d
    assert determinant.sign()!=0
    return ((c*e-b*f)/determinant,(a*f-c*d)/determinant)


def evaluate(l,p):return l[0]*p[0]+l[1]*p[1]-l[2]


if __name__=="__main__":
    zero,one=S2(),S2(F(1))
    s=S2(F(0),F(1))
    lines=[(zero,one,zero),(s-one,one,one),(one,one,one),
           (s+one,one,-one),(one,zero,-one),(-s-one,one,one),
           (-one,one,-one),(one-s,one,-one)]
    pairs={(i,j):meet(lines[i],lines[j]) for i,j in it.combinations(range(8),2)}
    point_support=defaultdict(set)
    for (i,j),p in pairs.items():point_support[p].update((i,j))
    assert all(len(s)<=3 for s in point_support.values())
    triples=[tuple(sorted(s)) for s in point_support.values() if len(s)==3]
    assert len(triples)==7
    triangles=[]
    used=defaultdict(list)
    for i,j,k in it.combinations(range(8),3):
        p,q,r=pairs[i,j],pairs[i,k],pairs[j,k]
        if len({p,q,r})<3:continue
        if all(not ({-1,1}<={evaluate(line,v).sign() for v in [p,q,r]}) for line in lines):
            triangle=(i,j,k)
            triangles.append(triangle)
            for l,u,v in [(i,p,q),(j,p,r),(k,q,r)]:
                edge=(l,frozenset((u,v)))
                used[edge].append(triangle)
    assert len(triangles)==14 and max(map(len,used.values()))==2
    shared=[(edge,tris) for edge,tris in used.items() if len(tris)==2]
    assert len(shared)==15
    output=dict(passed=True,n=8,triangles=14,triple_points=7,shared_segments=15,parallel_pairs=0,
                field="Q(sqrt(2)); each scalar is encoded [rational_part,sqrt2_coefficient]",
                line_convention="a*x+b*y=c",
                lines=[[[str(z.p),str(z.q)] for z in line] for line in lines],
                triple_supports=sorted(triples),triangle_triples=triangles,
                vertices=[dict(point=[x.encoded(),y.encoded()],support=sorted(s)) for (x,y),s in point_support.items()],
                shared_edges=[dict(line=l,endpoints=[list(sorted(point_support[p])) for p in endpoints],triangles=tris) for (l,endpoints),tris in shared],
                attribution="Furedi--Palasti phase-zero arrangement; new use refutes an auxiliary D<=2t conjecture",
                trust="Exact independent quadratic-field arithmetic; not a Lean theorem")
    out=ROOT/"research/openmath-seven-hour-2026-10-05/corpus/shared-rule8.json"
    out.write_text(json.dumps(output,indent=2)+"\n")
    print(json.dumps({k:output[k] for k in ["passed","n","triangles","triple_points","shared_segments","parallel_pairs","triple_supports"]}))
