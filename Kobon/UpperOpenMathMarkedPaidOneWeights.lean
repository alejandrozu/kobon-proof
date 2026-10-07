import Kobon.UpperOpenMathMarkedPaidZeroWeights

/-! A strict one-unit paid-curvature classification. An unmarked incident
edge at every poor target eliminates all such targets in the zero-cost,
single-full-one-cap case. This module is finite arithmetic; geometric
charging and degree extraction are separate actual-arrangement theorems. -/
namespace Kobon.UpperOpenMathMarkedPaidOneWeights
open Finset UpperOpenMathMarkedCurvatureWeights
open scoped BigOperators
set_option maxHeartbeats 1000000

theorem finite_paid_one_types {β : Type*} [DecidableEq β]
    (P : Finset β) (a d m : β → ℕ)
    (ha : ∀ p∈P, a p≤3) (had : ∀ p∈P, a p+d p≤6)
    (hfive : ∀ p∈P, a p+d p≠5) (hd : ∀ p∈P, d p≤5)
    (hext : ∀ p∈P, a p=3 → d p=3 ∧ m p=3)
    (hpartial : ∀ p∈P, a p=2 → d p=1 → 1≤m p)
    (hlow : ∀ p∈P, a p≤1 → m p=0)
    (noA : ∀ p∈P, ¬(a p=2 ∧ d p=4 ∧ m p=0))
    (oneB : (P.filter (fun p => a p=1 ∧ d p=5)).card=1)
    (capacity : (∑ p∈P, m p)+(P.filter (fun p => a p≤1 ∧ a p+d p≤2)).card≤
      ∑ p∈P.filter (fun p => a p≤1 ∧ a p+d p≤2), d p)
    (zero : (∑ p∈P, (6-2*(a p : ℤ)-d p))=0) :
    P.filter (fun p => a p≤1 ∧ a p+d p≤2)=∅ ∧
      (∀ p∈P, m p=0) ∧ (P.filter (fun p => a p=1 ∧ d p=3)).card=1 ∧
      ∀ p∈P, (a p=2 ∧ d p=2) ∨ (a p=1 ∧ d p=5) ∨ (a p=1 ∧ d p=3) := by
  classical
  let E := P.filter (fun p => a p=3)
  let A := P.filter (fun p => a p=2 ∧ d p=1)
  let B := P.filter (fun p => a p≤1 ∧ a p+d p≤2)
  let paid := fun p => 6-2*(a p : ℤ)-d p+unpaidWeight (a p) (d p) (m p)
  have unpaidEach (p : β) (hp : p∈P) : unpaidWeight (a p) (d p) (m p)=
      if a p=1 ∧ d p=5 then (1 : ℤ) else 0 := by
    unfold unpaidWeight
    rw [if_neg (noA p hp)]
  have unpaidSum : (∑ p∈P, unpaidWeight (a p) (d p) (m p))=1 := by
    rw [sum_congr rfl unpaidEach]
    have count : (∑ p∈P, if a p=1 ∧ d p=5 then (1 : ℤ) else 0)=
        ((P.filter (fun p => a p=1 ∧ d p=5)).card : ℤ) := by simp
    rw [count,oneB]
    norm_num
  have paidSum : (∑ p∈P, paid p)=1 := by
    change (∑ p∈P, (6-2*(a p : ℤ)-d p+unpaidWeight (a p) (d p) (m p)))=1
    rw [sum_add_distrib,zero,unpaidSum]
    norm_num
  have strongCapacity : (∑ p∈P, m p)+B.card≤∑ p∈B,d p := capacity
  have baseCapacity : (∑ p∈P, m p)≤∑ p∈B,d p := by omega
  have previous := finite_marked_curvature P a d m ha had hfive hext hpartial hlow baseCapacity
  change 3*(E.card : ℤ)+3*(A.card : ℤ)≤∑ p∈P,paid p at previous
  rw [paidSum] at previous
  have ez : E=∅ := card_eq_zero.mp (by omega)
  have az : A=∅ := card_eq_zero.mp (by omega)
  have noE (p : β) (hp : p∈P) : a p≠3 := by
    intro eq
    have hm : p∈E := mem_filter.mpr ⟨hp,eq⟩
    rw [ez] at hm
    exact notMem_empty p hm
  have noPartial (p : β) (hp : p∈P) : ¬(a p=2 ∧ d p=1) := by
    intro eq
    have hm : p∈A := mem_filter.mpr ⟨hp,eq⟩
    rw [az] at hm
    exact notMem_empty p hm
  let Q := fun p => paid p+2*m p-(if p∈B then 2*(d p : ℤ) else 0)
  have nonnegative (p : β) (hp : p∈P) : 0≤Q p := by
    have hap := ha p hp
    have hadp := had p hp
    have hfp := hfive p hp
    have hne := noE p hp
    have hna := noPartial p hp
    by_cases hb : p∈B
    · obtain ⟨hal,hsum⟩ := (mem_filter.mp hb).2
      have hm := hlow p hp hal
      dsimp [Q,paid]
      simp only [if_pos hb]
      unfold unpaidWeight
      split_ifs <;> omega
    · dsimp [Q,paid]
      simp only [if_neg hb]
      unfold unpaidWeight
      split_ifs <;> omega
  have bsub : B⊆P := filter_subset _ _
  have bsum : (∑ p∈P, (if p∈B then 2*(d p : ℤ) else 0))=2*∑ p∈B, (d p : ℤ) := by
    rw [← sum_filter,filter_mem_eq_inter,inter_eq_right.mpr bsub,mul_sum]
  have capZ : (∑ p∈P, (m p : ℤ))+(B.card : ℤ)≤∑ p∈B, (d p : ℤ) := by
    exact_mod_cast capacity
  have identity : (∑ p∈P, Q p)=1+2*(∑ p∈P, (m p : ℤ))-2*(∑ p∈B, (d p : ℤ)) := by
    change (∑ p∈P, (paid p+2*m p-(if p∈B then 2*(d p : ℤ) else 0)))=_
    rw [sum_sub_distrib,sum_add_distrib,paidSum,bsum,← mul_sum]
  have bEmpty : B=∅ := by
    have hnon := sum_nonneg nonnegative
    rw [identity] at hnon
    apply card_eq_zero.mp
    omega
  have marksZero : (∑ p∈P,m p)=0 := by
    change (∑ p∈P,m p)+B.card≤∑ p∈B,d p at capacity
    rw [bEmpty] at capacity
    simp only [card_empty,sum_empty,add_zero] at capacity
    omega
  have markedZero (p : β) (hp : p∈P) : m p=0 :=
    (sum_eq_zero_iff_of_nonneg (fun p hp => Nat.zero_le (m p))).mp marksZero p hp
  have paidNonnegative (p : β) (hp : p∈P) : 0≤paid p := by
    have nn := nonnegative p hp
    dsimp [Q] at nn
    rw [bEmpty,markedZero p hp] at nn
    simpa using nn
  have types (p : β) (hp : p∈P) :
      (a p=2 ∧ d p=2) ∨ (a p=1 ∧ d p=5) ∨ (a p=1 ∧ d p=3) := by
    have upper : paid p≤1 := by
      have h := single_le_sum paidNonnegative hp
      rwa [paidSum] at h
    have lower := paidNonnegative p hp
    have hap := ha p hp
    have hadp := had p hp
    have hfp := hfive p hp
    have hdp := hd p hp
    have hne := noE p hp
    have hna := noPartial p hp
    have ha24 := noA p hp
    have hm := markedZero p hp
    dsimp [paid] at upper lower
    rw [unpaidEach p hp] at upper lower
    omega
  have paidEach (p : β) (hp : p∈P) : paid p=if a p=1 ∧ d p=3 then (1 : ℤ) else 0 := by
    have un := unpaidEach p hp
    rcases types p hp with ⟨ha2,hd2⟩|⟨ha1,hd5⟩|⟨ha1,hd3⟩
    · dsimp [paid]
      rw [un,ha2,hd2]
      norm_num
    · dsimp [paid]
      rw [un,ha1,hd5]
      norm_num
    · dsimp [paid]
      rw [un,ha1,hd3]
      norm_num
  have count : ((P.filter (fun p => a p=1 ∧ d p=3)).card : ℤ)=1 := by
    have eachSum := sum_congr rfl paidEach
    rw [paidSum] at eachSum
    simpa using eachSum.symm
  exact ⟨bEmpty,markedZero,by exact_mod_cast count,types⟩

#print axioms finite_paid_one_types
end Kobon.UpperOpenMathMarkedPaidOneWeights
