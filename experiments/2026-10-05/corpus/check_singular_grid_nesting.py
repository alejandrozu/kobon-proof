"""Exact Q(sqrt3) tests for regular q6 parent roots inside q12 corridor fits.

Two cross-ratios characterize the five ordered parent roots. This is an exact
finite Möbius compatibility test, not a general geometric iteration theorem.
"""
from pathlib import Path
from fractions import Fraction as F
from dataclasses import dataclass
import itertools as it,json
ROOT=Path(__file__).resolve().parents[3]

@dataclass(frozen=True)
class Q3:
    a:F=F(0)
    b:F=F(0)
    def __add__(self,y):
        if not isinstance(y,Q3):y=Q3(F(y))
        return Q3(self.a+y.a,self.b+y.b)
    __radd__=__add__
    def __neg__(self):return Q3(-self.a,-self.b)
    def __sub__(self,y):return self+(-y if isinstance(y,Q3) else Q3(-F(y)))
    def __rsub__(self,y):return Q3(F(y))-self
    def __mul__(self,y):
        if not isinstance(y,Q3):y=Q3(F(y))
        return Q3(self.a*y.a+3*self.b*y.b,self.a*y.b+self.b*y.a)
    __rmul__=__mul__
    def __truediv__(self,y):
        if not isinstance(y,Q3):y=Q3(F(y))
        den=y.a*y.a-3*y.b*y.b;assert den
        return self*Q3(y.a/den,-y.b/den)
    def encoded(self):return [str(self.a),str(self.b)]

def crossratio(x,a,b,c):return (x-a)*(b-c)/((x-c)*(b-a))

if __name__=='__main__':
    s=Q3(F(0),F(1));roots=[-2-s,-s,Q3(F(-1)),-s/3,s-2,Q3(),2-s,s/3,Q3(F(1)),s,2+s];target=[-s,-s/3,Q3(),s/3,s]
    t3=crossratio(target[3],*target[:3]);t4=crossratio(target[4],*target[:3]);assert t3==Q3(F(-2)) and t4==Q3(F(-1))
    embeddings=[];cyclic_embeddings=[];target_pairs=set()
    for reversed_ in [False,True]:
        cycle=target[::-1] if reversed_ else target
        for rotation in range(5):
            ordered=cycle[rotation:]+cycle[:rotation]
            target_pairs.add((crossratio(ordered[3],*ordered[:3]),crossratio(ordered[4],*ordered[:3])))
    for ids in it.combinations(range(11),5):
        rr=[roots[i] for i in ids]
        if crossratio(rr[3],*rr[:3])==t3 and crossratio(rr[4],*rr[:3])==t4:embeddings.append(ids)
        if (crossratio(rr[3],*rr[:3]),crossratio(rr[4],*rr[:3])) in target_pairs:cyclic_embeddings.append(ids)
    report=json.loads((ROOT/'research/openmath-seven-hour-2026-10-05/seed_search/singular-corridor-grid/report.json').read_text());cases=[]
    for record in report['records']:
        if record['n']!=14 or not record.get('passed'):continue
        raw=json.loads((ROOT/record['proposal']).read_text());dup=set(raw['duplicate_ranks']);admissible=[e for e in embeddings if dup<=set(e)]
        cases.append(dict(source=record['source'],proposal=record['proposal'],axis_triangles=record['axis_triangles'],duplicate_ranks=sorted(dup),natural_even_grid_contains_both=dup<=set([1,3,5,7,9]),ordered_mobius_parent_embeddings=admissible,all_cyclic_mobius_parent_embeddings=[e for e in cyclic_embeddings if dup<=set(e)]))
    out=ROOT/'research/openmath-seven-hour-2026-10-05/corpus/singular-grid-nesting.json';result=dict(passed=True,field='Q(sqrt3), scalars encoded[rational,sqrt3coefficient]',all_ordered_q6_embeddings_into_q12_roots=[list(e) for e in embeddings],all_cyclic_q6_embeddings_into_q12_roots=[list(e) for e in cyclic_embeddings],fits=cases,total_sets_tested=462,target_crossratios=[t3.encoded(),t4.encoded()],scope='Exact five-root compatibility for every cyclic order and reflection; no arbitrary child type is excluded and no infinite construction is claimed')
    out.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result),flush=True)
