import Kobon.UpperOpenMathTripleCurvature

/-! Marked rays pay non-antipodal full two-cap triple fans. The remaining
negative correction counts unmarked (2,4) fans and full (1,5) fans.
The geometric marked-port budget is supplied by the actual extraction module. -/
namespace Kobon.UpperOpenMathMarkedCurvatureWeights
open Finset
open scoped BigOperators
set_option maxHeartbeats 1000000

def unpaidWeight (a d m : ℕ) : ℤ :=
  if a=2 ∧ d=4 ∧ m=0 then 2 else if a=1 ∧ d=5 then 1 else 0

theorem unpaidWeight_nonnegative (a d m : ℕ) : 0≤unpaidWeight a d m := by
  unfold unpaidWeight
  split_ifs <;> norm_num

theorem finite_marked_curvature {β : Type*} [DecidableEq β]
    (P : Finset β) (a d m : β → ℕ)
    (ha : ∀ p∈P, a p≤3) (had : ∀ p∈P, a p+d p≤6)
    (hfive : ∀ p∈P, a p+d p≠5)
    (hext : ∀ p∈P, a p=3 → d p=3 ∧ m p=3)
    (hpartial : ∀ p∈P, a p=2 → d p=1 → 1≤m p)
    (hlow : ∀ p∈P, a p≤1 → m p=0)
    (capacity : (∑ p∈P, m p)≤
      ∑ p∈P.filter (fun p => a p≤1 ∧ a p+d p≤2), d p) :
    3*((P.filter (fun p => a p=3)).card : ℤ)+
      3*((P.filter (fun p => a p=2 ∧ d p=1)).card : ℤ)≤
      ∑ p∈P, (6-2*(a p : ℤ)-d p+unpaidWeight (a p) (d p) (m p)) := by
  classical
  let E := P.filter (fun p => a p=3)
  let A := P.filter (fun p => a p=2 ∧ d p=1)
  let B := P.filter (fun p => a p≤1 ∧ a p+d p≤2)
  have esub : E⊆P := filter_subset _ _
  have asub : A⊆P := filter_subset _ _
  have bsub : B⊆P := filter_subset _ _
  have point (p : β) (hp : p∈P) :
      -2*(m p : ℤ)+(if p∈B then 2*(d p : ℤ) else 0)+
        3*(if p∈E then 1 else 0)+3*(if p∈A then 1 else 0)≤
        6-2*(a p : ℤ)-d p+unpaidWeight (a p) (d p) (m p) := by
    have hpa := ha p hp
    have hpd := had p hp
    have hpf := hfive p hp
    by_cases he : p∈E
    · have hap := (mem_filter.mp he).2
      have hdp := hext p hp hap
      have hb : p∉B := by intro hh; have hh' := (mem_filter.mp hh).2.1; omega
      have hpA : p∉A := by intro hh; have hh' := (mem_filter.mp hh).2.1; omega
      simp only [he,hb,hpA,ite_true,ite_false]
      unfold unpaidWeight
      split_ifs <;> omega
    · have hap : a p≠3 := fun hh => he (mem_filter.mpr ⟨hp,hh⟩)
      by_cases hb : p∈B
      · obtain ⟨hal,hadl⟩ := (mem_filter.mp hb).2
        have hm := hlow p hp hal
        have hpA : p∉A := by intro hh; have hh' := (mem_filter.mp hh).2.1; omega
        simp only [he,hb,hpA,ite_true,ite_false]
        unfold unpaidWeight
        split_ifs <;> omega
      · by_cases hpA : p∈A
        · obtain ⟨haa,hdd⟩ := (mem_filter.mp hpA).2
          have hmm := hpartial p hp haa hdd
          simp only [he,hb,hpA,ite_true,ite_false]
          unfold unpaidWeight
          split_ifs <;> omega
        · simp only [he,hb,hpA,ite_true,ite_false]
          unfold unpaidWeight
          split_ifs <;> omega
  have total := sum_le_sum point
  have ecount : (∑ p∈P, (if p∈E then (1 : ℤ) else 0))=E.card := by simp [inter_eq_right.mpr esub]
  have acount : (∑ p∈P, (if p∈A then (1 : ℤ) else 0))=A.card := by simp [inter_eq_right.mpr asub]
  have bcount : (∑ p∈P, (if p∈B then 2*(d p : ℤ) else 0))=2*∑ p∈B, (d p : ℤ) := by
    rw [← sum_filter,filter_mem_eq_inter,inter_eq_right.mpr bsub,mul_sum]
  simp only [sum_add_distrib,← mul_sum] at total
  rw [ecount,acount,bcount] at total
  have cap : (∑ p∈P, (m p : ℤ))≤∑ p∈B, (d p : ℤ) := by exact_mod_cast capacity
  change 3*(E.card : ℤ)+3*(A.card : ℤ)≤_
  rw [sum_add_distrib]
  linarith

set_option maxRecDepth 1000000 in
theorem finite_two_cap_non_antipodal_mark : ∀ O : Finset (ZMod 6),
    O.card=2 → (∀ z∈O, z+1∉O) →
    ¬(∃ a : ZMod 6, O={a,a+3}) →
    ∃ z : ZMod 6, z∉O ∧ z-1∈O ∧ z+1∈O := by
  decide +kernel

theorem finite_marked_zero_types {β : Type*} [DecidableEq β]
    (P : Finset β) (a d m : β → ℕ)
    (ha : ∀ p∈P, a p≤3) (had : ∀ p∈P, a p+d p≤6)
    (hfive : ∀ p∈P, a p+d p≠5)
    (hext : ∀ p∈P, a p=3 → d p=3 ∧ m p=3)
    (hpartial : ∀ p∈P, a p=2 → d p=1 → 1≤m p)
    (hlow : ∀ p∈P, a p≤1 → m p=0)
    (capacity : (∑ p∈P, m p)≤
      ∑ p∈P.filter (fun p => a p≤1 ∧ a p+d p≤2), d p)
    (unpaid : ∀ p∈P, unpaidWeight (a p) (d p) (m p)=0)
    (zero : (∑ p∈P, (6-2*(a p : ℤ)-d p))=0) :
    (∑ p∈P, m p)=∑ p∈P.filter (fun p => a p≤1 ∧ a p+d p≤2), d p ∧
    ∀ p∈P,
      (a p=2 ∧ d p=2 ∧ m p=0) ∨ (a p=2 ∧ d p=4 ∧ m p=1) ∨
      (a p=0 ∧ d p=2 ∧ m p=0) ∨ (a p=0 ∧ d p=6 ∧ m p=0) := by
  classical
  let E := P.filter (fun p => a p=3)
  let A := P.filter (fun p => a p=2 ∧ d p=1)
  let B := P.filter (fun p => a p≤1 ∧ a p+d p≤2)
  have previous := finite_marked_curvature P a d m ha had hfive hext hpartial hlow capacity
  have paidZero : (∑ p∈P, (6-2*(a p : ℤ)-d p+unpaidWeight (a p) (d p) (m p)))=0 := by
    rw [sum_congr rfl (fun p hp => by rw [unpaid p hp,add_zero])]
    exact zero
  rw [paidZero] at previous
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
  let Q := fun p => (6-2*(a p : ℤ)-d p)+2*m p-(if p∈B then 2*(d p : ℤ) else 0)
  have nonnegative (p : β) (hp : p∈P) : 0≤Q p := by
    have hap := ha p hp
    have hadp := had p hp
    have hfp := hfive p hp
    have hne := noE p hp
    have hna := noA p hp
    have hup := unpaid p hp
    unfold unpaidWeight at hup
    by_cases hb : p∈B
    · obtain ⟨hal,hsum⟩ := (mem_filter.mp hb).2
      have hm := hlow p hp hal
      dsimp [Q]
      simp only [if_pos hb]
      split_ifs at hup <;> omega
    · dsimp [Q]
      simp only [if_neg hb]
      split_ifs at hup <;> omega
  have bsub : B⊆P := filter_subset _ _
  have bsum : (∑ p∈P, (if p∈B then 2*(d p : ℤ) else 0))=2*∑ p∈B, (d p : ℤ) := by
    rw [← sum_filter,filter_mem_eq_inter,inter_eq_right.mpr bsub,mul_sum]
  have capZ : (∑ p∈P, (m p : ℤ))≤∑ p∈B, (d p : ℤ) := by exact_mod_cast capacity
  have identity : (∑ p∈P, Q p)=2*(∑ p∈P, (m p : ℤ))-2*(∑ p∈B, (d p : ℤ)) := by
    change (∑ p∈P, ((6-2*(a p : ℤ)-d p)+2*m p-(if p∈B then 2*(d p : ℤ) else 0)))=_
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
  have hup := unpaid p hp
  have hz := each p hp
  unfold unpaidWeight at hup
  by_cases hb : p∈B
  · obtain ⟨hal,hsum⟩ := (mem_filter.mp hb).2
    have hm := hlow p hp hal
    dsimp [Q] at hz
    simp only [if_pos hb] at hz
    split_ifs at hup <;> omega
  · have hnot : ¬(a p≤1 ∧ a p+d p≤2) := fun hh => hb (mem_filter.mpr ⟨hp,hh⟩)
    have hmlow := hlow p hp
    dsimp [Q] at hz
    simp only [if_neg hb] at hz
    split_ifs at hup <;> omega

#print axioms finite_marked_curvature
#print axioms finite_two_cap_non_antipodal_mark
#print axioms finite_marked_zero_types
end Kobon.UpperOpenMathMarkedCurvatureWeights
