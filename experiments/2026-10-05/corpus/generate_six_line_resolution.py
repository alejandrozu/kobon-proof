"""Generate ordinary kernel proofs of all six-line supporting-triple cases.

The generator selects finite case branches; Lean independently proves every
inequality for the entire open interval0<epsilon<1/100. No native computation
or trust in the generator establishes the theorem.
"""
from pathlib import Path
from fractions import Fraction as F
import sys,itertools as it
ROOT=Path(__file__).resolve().parents[3];sys.path.insert(0,str(ROOT/'research/kobon-hybrid'))
from exact_geometry import arrangement
OLD=[(0,1,0),(1,-1,0),(1,1,0),(1,2,3),(-2,1,2),(1,4,-4)]

def tri(t):return '⟨'+','.join(map(str,t))+'⟩'
def finset(ts):return '{'+','.join(map(tri,ts))+'}'
def orient(r,l,m):
    a,b,c=l;d,e,f=m;u,v,z=r;det=a*e-b*d
    return (u*(c*e-b*f)+v*(a*f-c*d)-z*det)*det
def area(r,l,m):
    a,b,c=l;d,e,f=m;u,v,z=r
    return u*(c*e-b*f)+v*(a*f-c*d)-z*(a*e-b*d)

ALL=list(it.combinations(range(6),3));text=['import Kobon.Cells','import Kobon.Simple','import Mathlib.Tactic.FinCases','import Mathlib.Tactic.NormNum','import Mathlib.Tactic.Linarith','','/-! Exact interval witnesses for an isolated triple resolution. The three old','central triangles occupy alternating radial sectors. For every0<ε<1/100,','moving the horizontal line up changes6 to7 triangles; moving it down changes','6 to4. Thus a reverse codimension-one collapse can gain2. These are concrete','geometry theorems, not an assumed general desingularization calculus. -/','namespace Kobon.OpenMathSixLineResolution','open Cells','', 'def arrangement (ε : ℝ) : ℕ → Line ℝ','  | 0 => ⟨0,1,ε⟩','  | 1 => ⟨1,-1,0⟩','  | 2 => ⟨1,1,0⟩','  | 3 => ⟨1,2,3⟩','  | 4 => ⟨-2,1,2⟩','  | _ => ⟨1,4,-4⟩','',f'def all6 : Finset Triple := {finset(ALL)}','noncomputable def triangles (L : ℕ → Line ℝ) : Finset Triple := by','  classical','  exact all6.filter (TrianglePredicate 6 L)','', 'theorem ordered_member (t : Triple) (hi : t.i<t.j) (hj : t.j<t.k) (hk : t.k<6) :','    t∈all6 := by','  rcases t with ⟨i,j,k⟩','  simp only [all6,Finset.mem_insert,Finset.mem_singleton,Triple.mk.injEq]','  dsimp at hi hj hk','  omega','']
for name,sample,param in [('old',F(0),'0'),('up',F(1,1000),'ε'),('down',F(-1,1000),'-ε')]:
    ll=OLD.copy();ll[0]=(0,1,sample);ts=sorted(arrangement(ll)['triangles']);text += [f'def {name}Triangles : Finset Triple := {finset(ts)}','']
    args='' if name=='old' else '(ε : ℝ) (he : 0<ε) (hs : ε<1/100) '
    text += [f'theorem {name}_triangle_iff {args}(t : Triple) :',f'    TrianglePredicate 6 (arrangement ({param})) t ↔ t∈{name}Triangles := by','  constructor','  · intro ht','    have hm := ordered_member t ht.1 ht.2.1 ht.2.2.1','    simp only [all6,Finset.mem_insert,Finset.mem_singleton] at hm','    rcases hm with '+ '|'.join(['rfl']*len(ALL))]
    for Q in ALL:
        if Q in ts:text.append(f'    · simp [{name}Triangles]');continue
        i,j,k=Q
        if area(ll[k],ll[i],ll[j])==0:
            text += ['    · have hd := ht.2.2.2.1','      norm_num [arrangement,evalVertex,vertex,det] at hd'];continue
        rs=[]
        for r in range(6):
            vals=[orient(ll[r],ll[a],ll[b]) for a,b in it.combinations(Q,2)]
            if min(vals)<0<max(vals):rs.append(r)
        r=rs[0];text += [f'    · have hh := ht.2.2.2.2 ⟨{r},by decide⟩','      rcases hh with ⟨ha,hb,hc⟩|⟨ha,hb,hc⟩','      all_goals simp_all [arrangement,orientedEval,evalVertex,vertex,det]','      all_goals linarith']
    text += ['  · intro hm',f'    simp only [{name}Triangles,Finset.mem_insert,Finset.mem_singleton] at hm','    rcases hm with '+'|'.join(['rfl']*len(ts))]
    for Q in ts:
        text += ['    · refine ⟨by decide,by decide,by decide,?_,?_⟩','      · norm_num [arrangement,evalVertex,vertex,det]','        all_goals linarith','      · intro r; fin_cases r']
        for r in range(6):
            vals=[orient(ll[r],ll[a],ll[b]) for a,b in it.combinations(Q,2)];side='inl' if min(vals)>=0 else 'inr';text += [f'        · refine Or.{side} ⟨?_,?_,?_⟩ <;>','            norm_num [arrangement,orientedEval,evalVertex,vertex,det] <;> linarith']
    text.append('')
text += ['theorem triangle_set_complete (L : ℕ → Line ℝ) (t : Triple) :','    t∈triangles L ↔ TrianglePredicate 6 L t := by','  classical','  simp only [triangles,Finset.mem_filter]','  exact ⟨fun h=>h.2,fun h=>⟨ordered_member t h.1 h.2.1 h.2.2.1,h⟩⟩','']
for name,param,count in [('old','0',6),('up','ε',7),('down','-ε',4)]:
    args='' if name=='old' else '(ε : ℝ) (he : 0<ε) (hs : ε<1/100) '
    use=f'{name}_triangle_iff' if name=='old' else f'{name}_triangle_iff ε he hs'
    text += [f'theorem {name}_set {args}: triangles (arrangement ({param}))={name}Triangles := by','  classical','  ext t',f'  simp only [triangle_set_complete,{use}]','',f'theorem {name}_count {args}: (triangles (arrangement ({param}))).card={count} := by',f'  rw [{name}_set'+(']' if name=='old' else ' ε he hs]'),'  decide','']
text += ['theorem reversal_gain_two (ε : ℝ) (he : 0<ε) (hs : ε<1/100) :','    (triangles (arrangement 0)).card=(triangles (arrangement (-ε))).card+2 := by','  rw [old_count,down_count ε he hs]','','def broken : Finset Triple := {⟨0,1,3⟩,⟨0,2,4⟩,⟨1,2,5⟩}','', 'theorem upward_keeps_all : upTriangles=oldTriangles∪{⟨0,1,2⟩} := by','  decide','', 'theorem downward_breaks_three : downTriangles=(oldTriangles\u005c\u005cbroken)∪{⟨0,1,2⟩} := by','  decide','', 'theorem broken_card : broken.card=3 := by decide','', 'noncomputable def interior (t : Triple) : Set Point :=','  OpenTriangle (intersection (arrangement 0 t.i) (arrangement 0 t.j))','    (intersection (arrangement 0 t.i) (arrangement 0 t.k))','    (intersection (arrangement 0 t.j) (arrangement 0 t.k))','']
for Q,name,ineqs in [((0,1,3),'sector_zero',['0<p.2','0<p.1-p.2']),((0,2,4),'sector_two',['0<p.2','p.1+p.2<0']),((1,2,5),'sector_four',['p.2<0','0<p.1-p.2','p.1+p.2<0'])]:
    text += [f'theorem {name} (p : Point) (hp : p∈interior {tri(Q)}) :','    '+' ∧ '.join(ineqs)+' := by','  rcases hp with ⟨u,v,w,hu,hv,hw,hs,rfl⟩','  norm_num [arrangement,intersection,vertex,det,barycenter]','  constructor <;> try constructor <;> positivity']
text += ['', '#print axioms up_triangle_iff','#print axioms down_triangle_iff','#print axioms reversal_gain_two','#print axioms downward_breaks_three','end Kobon.OpenMathSixLineResolution']
rendered='\n'.join(text)+'\n'
rendered=rendered.replace('import Mathlib.Tactic.Linarith\n','import Mathlib.Tactic.Linarith\nimport Mathlib.Tactic.IntervalCases\n')
rendered=rendered.replace('  omega\n','  have h1 : i≤3 := by omega\n  have h2 : j≤4 := by omega\n  have h3 : k≤5 := by omega\n  interval_cases i <;> interval_cases j <;> interval_cases k <;> simp_all\n',1)
rendered=rendered.replace('oldTriangles'+chr(92)*2+'broken','oldTriangles.filter fun t => t∉broken')
rendered=rendered.replace('  constructor <;> try constructor <;> positivity','  constructor <;> nlinarith',2)
rendered=rendered.replace('  constructor <;> try constructor <;> positivity','  refine ⟨?_,?_,?_⟩ <;> nlinarith')
extra=['theorem no_parallel (ε : ℝ) : NoParallel 6 (arrangement ε) := by',
    '  intro i j hij','  change i.val<j.val at hij','  fin_cases i <;> fin_cases j',
    '  all_goals norm_num at hij','  all_goals norm_num [arrangement,det]','',
    'theorem old_unique_triple (t : Triple) (hi : t.i<t.j) (hj : t.j<t.k) (hk : t.k<6) :',
    '    evalVertex (arrangement 0 t.k) (arrangement 0 t.i) (arrangement 0 t.j)=0 ↔ t=⟨0,1,2⟩ := by',
    '  have hm := ordered_member t hi hj hk',
    '  simp only [all6,Finset.mem_insert,Finset.mem_singleton] at hm',
    '  rcases hm with '+'|'.join(['rfl']*len(ALL)),
    '  all_goals norm_num [arrangement,evalVertex,vertex,det,Triple.mk.injEq]','']
for name,param in [('up','ε'),('down','-ε')]:
    extra += [f'theorem {name}_nondegenerate (ε : ℝ) (he : 0<ε) (hs : ε<1/100)',
        '    (t : Triple) (hi : t.i<t.j) (hj : t.j<t.k) (hk : t.k<6) :',
        f'    evalVertex (arrangement ({param}) t.k) (arrangement ({param}) t.i) (arrangement ({param}) t.j)≠0 := by',
        '  have hm := ordered_member t hi hj hk',
        '  simp only [all6,Finset.mem_insert,Finset.mem_singleton] at hm',
        '  rcases hm with '+'|'.join(['rfl']*len(ALL)),
        '  all_goals norm_num [arrangement,evalVertex,vertex,det]',
        '  all_goals linarith','',
        f'theorem {name}_no_concurrent (ε : ℝ) (he : 0<ε) (hs : ε<1/100) :',
        f'    NoConcurrent 6 (arrangement ({param})) := by',
        '  intro i j k hij hjk',
        f'  exact {name}_nondegenerate ε he hs ⟨i.val,j.val,k.val⟩ hij hjk k.isLt','']
extra += ['#print axioms no_parallel','#print axioms old_unique_triple','#print axioms up_no_concurrent','#print axioms down_no_concurrent','']
rendered=rendered.replace('#print axioms up_triangle_iff','\n'.join(extra)+'\n#print axioms up_triangle_iff')
(ROOT/'Kobon/OpenMathSixLineResolution.lean').write_text(rendered,encoding='utf-8');print('Generated',len(rendered.splitlines()),'lines')
