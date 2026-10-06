"""Generate all 24 nondegenerate three-corner cases of a strict diagonal quad."""
from pathlib import Path
from itertools import permutations
ROOT=Path(__file__).resolve().parents[3]
prefix='''import Kobon.UpperOpenMathCevianCrossing

/-! Any three outer corners of a strict antipodal star bound its center. -/
namespace Kobon.UpperOpenMathQuadThreeBoundary
open Cells UpperOpenMathAntipodalCenterUniqueness UpperOpenMathCevianCrossing
set_option maxHeartbeats 1000000

theorem area_between_zero (p q c : Point) (bet : Between c p q) : areaDet p q c=0 := by
  obtain ⟨u,v,hu,hv,he⟩ := between_area p q c p q bet
  have pp : areaDet p q p=0 := by unfold areaDet; ring
  have qq : areaDet p q q=0 := by unfold areaDet; ring
  rw [pp,qq] at he
  simpa using he

theorem four_corner_areas_positive (c p q r s : Point) (pos : 0<areaDet c p q)
    (pr : Between c p r) (qs : Between c q s) :
    0<areaDet p q r ∧ 0<areaDet p q s ∧ 0<areaDet p r s ∧ 0<areaDet q r s := by
  have pqc : areaDet p q c=areaDet c p q := by unfold areaDet; ring
  have pqP : areaDet p q p=0 := by unfold areaDet; ring
  have pqQ : areaDet p q q=0 := by unfold areaDet; ring
  have pqr : 0<areaDet p q r := by
    obtain ⟨u,v,hu,hv,he⟩ := between_area p q c p r pr
    rw [pqc,pqP] at he
    by_contra h
    have le : areaDet p q r≤0 := le_of_not_gt h
    have nonpos := mul_nonpos_of_nonneg_of_nonpos hv.le le
    linarith
  have pqs : 0<areaDet p q s := by
    obtain ⟨u,v,hu,hv,he⟩ := between_area p q c q s qs
    rw [pqc,pqQ] at he
    by_contra h
    have le : areaDet p q s≤0 := le_of_not_gt h
    have nonpos := mul_nonpos_of_nonneg_of_nonpos hv.le le
    linarith
  have prs : 0<areaDet p r s := by
    obtain ⟨u,v,hu,hv,he⟩ := between_area p r c q s qs
    have prq : areaDet p r q= -areaDet p q r := by unfold areaDet; ring
    rw [area_between_zero p r c pr,prq] at he
    by_contra h
    have le : areaDet p r s≤0 := le_of_not_gt h
    have nonpos := mul_nonpos_of_nonneg_of_nonpos hv.le le
    have positive := mul_pos hu pqr
    nlinarith
  have qrs : 0<areaDet q r s := by
    obtain ⟨u,v,hu,hv,he⟩ := between_area q s c p r pr
    have qsp : areaDet q s p=areaDet p q s := by unfold areaDet; ring
    have qsr : areaDet q s r= -areaDet q r s := by unfold areaDet; ring
    rw [area_between_zero q s c qs,qsp,qsr] at he
    by_contra h
    have le : areaDet q r s≤0 := le_of_not_gt h
    have nonneg := mul_nonneg hv.le (neg_nonneg.mpr le)
    have positive := mul_pos hu pqs
    linarith
  exact ⟨pqr,pqs,prs,qrs⟩

theorem three_corner_boundary (c p q r s a b e : Point)
    (pos : 0<areaDet c p q) (pr : Between c p r) (qs : Between c q s)
    (ma : a=p∨a=q∨a=r∨a=s) (mb : b=p∨b=q∨b=r∨b=s)
    (me : e=p∨e=q∨e=r∨e=s) (ab : a≠b) (ae : a≠e) (be : b≠e) :
    areaDet a b e≠0 ∧ (Between c a b∨Between c a e∨Between c b e) := by
  obtain ⟨pqr,pqs,prs,qrs⟩ := four_corner_areas_positive c p q r s pos pr qs
'''
names=['p','q','r','s'];posnames={(0,1,2):'pqr',(0,1,3):'pqs',(0,2,3):'prs',(1,2,3):'qrs'}
lines=[prefix]
perms=list(permutations(range(4),3))
for j,perm in enumerate(perms):
    base=tuple(sorted(perm));inv=sum(perm[a]>perm[b] for a in range(3) for b in range(a+1,3));sign='-' if inv%2 else ''
    A=' '.join(names[i] for i in perm);B=' '.join(names[i] for i in base)
    lines+=[f'  have hn{j} : areaDet {A}≠0 := by',f'    have eq : areaDet {A}={sign}areaDet {B} := by unfold areaDet; ring','    rw [eq]',f'    exact '+('neg_ne_zero.mpr ' if sign else '')+f'(ne_of_gt {posnames[base]})']
lines+=['  rcases ma with ha|ha|ha|ha <;> rcases mb with hb|hb|hb|hb <;> rcases me with he|he|he|he','  all_goals simp only [ha,hb,he] at ab ae be ⊢','  all_goals first','    | exact False.elim (ab rfl)','    | exact False.elim (ae rfl)','    | exact False.elim (be rfl)']
for j,perm in enumerate(perms):
    pair=(0,2) if {0,2}<=set(perm) else (1,3);lemma='pr' if pair==(0,2) else 'qs';a,b=sorted((perm.index(pair[0]),perm.index(pair[1])))
    if perm[a]!=pair[0]:lemma+='.symm'
    beta=f'Or.inl {lemma}' if (a,b)==(0,1) else f'Or.inr (Or.inl {lemma})' if (a,b)==(0,2) else f'Or.inr (Or.inr {lemma})'
    lines.append(f'    | exact ⟨hn{j},{beta}⟩')
lines+=['','#print axioms three_corner_boundary','end Kobon.UpperOpenMathQuadThreeBoundary','']
(ROOT/'Kobon/UpperOpenMathQuadThreeBoundary.lean').write_text('\n'.join(lines),encoding='utf-8')
print('Generated strict three-corner boundary proof.')
