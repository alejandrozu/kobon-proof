import Kobon.UpperOpenMathMarkedCurvatureWeights

/-! Exact equality classification for the entire paid curvature sum.
The unmarked full two-cap and full one-cap classes remain explicit. -/
namespace Kobon.UpperOpenMathMarkedPaidZeroWeights
open Finset UpperOpenMathMarkedCurvatureWeights
open scoped BigOperators
set_option maxHeartbeats 1000000

theorem finite_paid_zero_types {β : Type*} [DecidableEq β]
    (P : Finset β) (a d m : β → ℕ)
    (ha : ∀ p∈P, a p≤3) (had : ∀ p∈P, a p+d p≤6)
    (hfive : ∀ p∈P, a p+d p≠5)
    (hext : ∀ p∈P, a p=3 → d p=3 ∧ m p=3)
    (hpartial : ∀ p∈P, a p=2 → d p=1 → 1≤m p)
    (hlow : ∀ p∈P, a p≤1 → m p=0)
    (capacity : (∑ p∈P, m p)≤
      ∑ p∈P.filter (fun p => a p≤1 ∧ a p+d p≤2), d p)
    (zero : (∑ p∈P, (6-2*(a p : ℤ)-d p+unpaidWeight (a p) (d p) (m p)))=0) :
    (∑ p∈P, m p)=∑ p∈P.filter (fun p => a p≤1 ∧ a p+d p≤2), d p ∧
    ∀ p∈P,
      (a p=2 ∧ d p=2 ∧ m p=0) ∨ (a p=2 ∧ d p=4 ∧ m p=1) ∨
      (a p=0 ∧ d p=2 ∧ m p=0) ∨ (a p=0 ∧ d p=6 ∧ m p=0) ∨
      (a p=2 ∧ d p=4 ∧ m p=0) ∨ (a p=1 ∧ d p=5 ∧ m p=0) := by
  classical
  let E := P.filter (fun p => a p=3)
  let A := P.filter (fun p => a p=2 ∧ d p=1)
  let B := P.filter (fun p => a p≤1 ∧ a p+d p≤2)
  have previous := finite_marked_curvature P a d m ha had hfive hext hpartial hlow capacity
  rw [zero] at previous
  change 3*(E.card : ℤ)+3*(A.card : ℤ)≤0 at previous
  have ez : E=∅ := card_eq_zero.mp (by omega)
  have az : A=∅ := card_eq_zero.mp (by omega)
  have noE (p : β) (hp : p∈P) : a p≠3 := by
    intro hh
    have hm : p∈E := mem_filter.mpr ⟨hp,hh⟩
    rw [ez] at hm
    exact notMem_empty p hm
  have noA (p : β) (hp : p∈P) : ¬(a p=2 ∧ d p=1) := by
    intro hh
    have hm : p∈A := mem_filter.mpr ⟨hp,hh⟩
    rw [az] at hm
    exact notMem_empty p hm
  let Q := fun p => (6-2*(a p : ℤ)-d p+unpaidWeight (a p) (d p) (m p))+2*m p-(if p∈B then 2*(d p : ℤ) else 0)
  have nonnegative (p : β) (hp : p∈P) : 0≤Q p := by
    have hap := ha p hp
    have hadp := had p hp
    have hfp := hfive p hp
    have hne := noE p hp
    have hna := noA p hp
    by_cases hb : p∈B
    · obtain ⟨hal,hsum⟩ := (mem_filter.mp hb).2
      have hm := hlow p hp hal
      dsimp [Q]
      simp only [if_pos hb]
      unfold unpaidWeight
      split_ifs <;> omega
    · dsimp [Q]
      simp only [if_neg hb]
      unfold unpaidWeight
      split_ifs <;> omega
  have bsub : B⊆P := filter_subset _ _
  have bsum : (∑ p∈P, (if p∈B then 2*(d p : ℤ) else 0))=2*∑ p∈B, (d p : ℤ) := by
    rw [← sum_filter,filter_mem_eq_inter,inter_eq_right.mpr bsub,mul_sum]
  have capZ : (∑ p∈P, (m p : ℤ))≤∑ p∈B, (d p : ℤ) := by exact_mod_cast capacity
  have identity : (∑ p∈P, Q p)=2*(∑ p∈P, (m p : ℤ))-2*(∑ p∈B, (d p : ℤ)) := by
    change (∑ p∈P, ((6-2*(a p : ℤ)-d p+unpaidWeight (a p) (d p) (m p))+2*m p-(if p∈B then 2*(d p : ℤ) else 0)))=_
    rw [sum_sub_distrib,sum_add_distrib,zero,bsum,← mul_sum]
    ring
  have qzero : (∑ p∈P, Q p)=0 := by
    have hnon := sum_nonneg nonnegative
    rw [identity] at hnon ⊢
    omega
  have capEqZ : (∑ p∈P, (m p : ℤ))=∑ p∈B, (d p : ℤ) := by
    rw [identity] at qzero
    omega
  have each := (sum_eq_zero_iff_of_nonneg nonnegative).mp qzero
  refine ⟨by exact_mod_cast capEqZ,?_⟩
  intro p hp
  have hap := ha p hp
  have hadp := had p hp
  have hfp := hfive p hp
  have hne := noE p hp
  have hna := noA p hp
  have hz := each p hp
  by_cases hb : p∈B
  · obtain ⟨hal,hsum⟩ := (mem_filter.mp hb).2
    have hm := hlow p hp hal
    have hnot1 : ¬(a p=2 ∧ d p=4 ∧ m p=0) := by omega
    have hnot2 : ¬(a p=1 ∧ d p=5) := by omega
    dsimp [Q] at hz
    simp only [if_pos hb,unpaidWeight,if_neg hnot1,if_neg hnot2] at hz
    have ah : a p=0 := by omega
    have dh : d p=2 := by omega
    exact Or.inr (Or.inr (Or.inl ⟨ah,dh,hm⟩))
  · have hnot : ¬(a p≤1 ∧ a p+d p≤2) := fun hh => hb (mem_filter.mpr ⟨hp,hh⟩)
    have hmlow := hlow p hp
    dsimp [Q] at hz
    simp only [if_neg hb] at hz
    by_cases hA : a p=2 ∧ d p=4 ∧ m p=0
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hA))))
    by_cases hV : a p=1 ∧ d p=5
    · have hm : m p=0 := hmlow (by omega)
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hV.1,hV.2,hm⟩))))
    simp only [unpaidWeight,if_neg hA,if_neg hV] at hz
    by_cases ha2 : a p=2
    · by_cases hd4 : d p=4
      · have hm : m p=1 := by omega
        exact Or.inr (Or.inl ⟨ha2,hd4,hm⟩)
      · have hd2 : d p=2 := by omega
        have hm : m p=0 := by omega
        exact Or.inl ⟨ha2,hd2,hm⟩
    · have hal : a p≤1 := by omega
      have hm := hmlow hal
      have ha0 : a p=0 := by omega
      have hd6 : d p=6 := by omega
      exact Or.inr (Or.inr (Or.inr (Or.inl ⟨ha0,hd6,hm⟩)))

#print axioms finite_paid_zero_types
end Kobon.UpperOpenMathMarkedPaidZeroWeights
