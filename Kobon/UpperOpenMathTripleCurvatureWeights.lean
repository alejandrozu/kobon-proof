import Kobon.UpperOpenMathTripleDegreeThree

/-! Unrestricted triple-fan curvature. The only uncompensated negative
types have ordinary/core shared degrees (2,4) or (1,5). The extremal
(3,3) type is paid by its actual poor neighbors in the geometric wrapper.
This finite algebra uses no maximum-degree assumption. -/
namespace Kobon.UpperOpenMathTripleCurvatureWeights
open Finset
open scoped BigOperators
set_option maxHeartbeats 1000000

def badWeight (a d : ℕ) : ℤ :=
  if a=2 ∧ d=4 then 2 else if a=1 ∧ d=5 then 1 else 0

theorem finite_curvature_discharge {β : Type*} [DecidableEq β]
    (P : Finset β) (a d : β → ℕ)
    (ha : ∀ p∈P, a p≤3) (had : ∀ p∈P, a p+d p≤6)
    (hfive : ∀ p∈P, a p+d p≠5)
    (hext : ∀ p∈P, a p=3 → d p=3)
    (capacity : 3*(P.filter (fun p => a p=3)).card≤
      ∑ p∈P.filter (fun p => a p≤1 ∧ a p+d p≤2), d p) :
    0≤∑ p∈P, (6-2*(a p : ℤ)-d p+badWeight (a p) (d p)) ∧
    ((∑ p∈P, (6-2*(a p : ℤ)-d p+badWeight (a p) (d p)))=0 →
      ∀ p∈P, (a p=2 ∧ d p=2) ∨ (a p=0 ∧ d p=6) ∨
        (a p=2 ∧ d p=4) ∨ (a p=1 ∧ d p=5)) := by
  classical
  let E := P.filter (fun p => a p=3)
  let B := P.filter (fun p => a p≤1 ∧ a p+d p≤2)
  have esub : E⊆P := filter_subset _ _
  have bsub : B⊆P := filter_subset _ _
  have hPoint (p : β) (hp : p∈P) :
      -(3 : ℤ)*(if p∈E then 1 else 0)+(if p∈B then (d p : ℤ)+2 else 0)≤
        6-2*(a p : ℤ)-d p+badWeight (a p) (d p) := by
    have hpa := ha p hp
    have hpd := had p hp
    have hpf := hfive p hp
    by_cases he : p∈E
    · have hap := (mem_filter.mp he).2
      have hdp := hext p hp hap
      have hb : p∉B := by intro hh; have hh' := (mem_filter.mp hh).2.1; omega
      simp only [he,hb,ite_true,ite_false]
      simp only [badWeight,hap,hdp]; norm_num
    · have hap : a p≠3 := fun hh => he (mem_filter.mpr ⟨hp,hh⟩)
      by_cases hb : p∈B
      · have hab := (mem_filter.mp hb).2
        simp only [he,hb,ite_true,ite_false]
        unfold badWeight
        split_ifs <;> omega
      · simp only [he,hb,ite_true,ite_false]
        unfold badWeight
        split_ifs <;> omega
  have hSum := sum_le_sum hPoint
  have hecount : (∑ p∈P, (if p∈E then (1 : ℤ) else 0))=E.card := by
    simp [inter_eq_right.mpr esub]
  have hbcount : (∑ p∈P, (if p∈B then (d p : ℤ)+2 else 0))=
      (∑ p∈B, (d p : ℤ))+2*B.card := by
    rw [← sum_filter,filter_mem_eq_inter,inter_eq_right.mpr bsub,sum_add_distrib]
    simp [mul_comm]
  simp only [sum_add_distrib,← mul_sum] at hSum
  rw [hecount,hbcount] at hSum
  rw [← sum_add_distrib] at hSum
  have hc : 3*(E.card : ℤ)≤∑ p∈B, (d p : ℤ) := by exact_mod_cast capacity
  have hbpos : 0≤(B.card : ℤ) := by positivity
  constructor
  · linarith
  · intro hz
    have hbzero : B=∅ := card_eq_zero.mp (by omega)
    have hezero : E=∅ := by
      simp only [hbzero,sum_empty] at hc
      exact card_eq_zero.mp (by omega)
    have hap (p : β) (hp : p∈P) : a p≠3 := by
      intro hh
      have hpe : p∈E := mem_filter.mpr ⟨hp,hh⟩
      rw [hezero] at hpe
      exact notMem_empty p hpe
    have hnonneg (p : β) (hp : p∈P) :
        (0 : ℤ)≤6-2*(a p : ℤ)-d p+badWeight (a p) (d p) := by
      have hpa := ha p hp
      have hpd := had p hp
      have hpf := hfive p hp
      have hpe := hap p hp
      unfold badWeight
      split_ifs <;> omega
    have hzero := (sum_eq_zero_iff_of_nonneg hnonneg).mp hz
    intro p hp
    have hpa := ha p hp
    have hpd := had p hp
    have hpf := hfive p hp
    have hpe := hap p hp
    have hw := hzero p hp
    unfold badWeight at hw
    split_ifs at hw <;> omega

theorem finite_good_curvature {β : Type*} [DecidableEq β]
    (P : Finset β) (a d : β → ℕ)
    (ha : ∀ p∈P, a p≤3) (had : ∀ p∈P, a p+d p≤6)
    (hfive : ∀ p∈P, a p+d p≠5)
    (hext : ∀ p∈P, a p=3 → d p=3)
    (good : ∀ p∈P, ¬(a p=2 ∧ d p=4) ∧ ¬(a p=1 ∧ d p=5))
    (capacity : 3*(P.filter (fun p => a p=3)).card≤
      ∑ p∈P.filter (fun p => a p≤1 ∧ a p+d p≤2), d p) :
    0≤∑ p∈P, (6-2*(a p : ℤ)-d p) ∧
    ((∑ p∈P, (6-2*(a p : ℤ)-d p))=0 →
      ∀ p∈P, (a p=2 ∧ d p=2) ∨ (a p=0 ∧ d p=6)) := by
  have h := finite_curvature_discharge P a d ha had hfive hext capacity
  have hw (p : β) (hp : p∈P) : badWeight (a p) (d p)=0 := by
    simp only [badWeight,if_neg (good p hp).1,if_neg (good p hp).2]
  have he : (∑ p∈P, (6-2*(a p : ℤ)-d p+badWeight (a p) (d p)))=
      ∑ p∈P, (6-2*(a p : ℤ)-d p) :=
    sum_congr rfl (fun p hp => by rw [hw p hp,add_zero])
  rw [he] at h
  refine ⟨h.1,?_⟩
  intro hz p hp
  have hx := h.2 hz p hp
  rcases hx with hx|hx|hx|hx
  · exact Or.inl hx
  · exact Or.inr hx
  · exact False.elim ((good p hp).1 hx)
  · exact False.elim ((good p hp).2 hx)

#print axioms finite_curvature_discharge
#print axioms finite_good_curvature
end Kobon.UpperOpenMathTripleCurvatureWeights
