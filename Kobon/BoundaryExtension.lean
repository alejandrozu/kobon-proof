import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

/-!
The finite cyclic counting core of a geometric extension argument.
This file does NOT assume or prove the universal Kobon recurrence.
The geometric identification of wedges, unused edges and cyclic directions
is proved in the accompanying manuscript, not formalized here.
-/

namespace KobonBoundary

def capCount {N : ℕ} (width : ℕ)
    (B : Finset (ZMod N)) (j : ZMod N) : ℕ :=
  ∑ k ∈ Finset.range width, if j + (k : ZMod N) ∈ B then 1 else 0

theorem cap_mass {N : ℕ} [NeZero N] (width : ℕ)
    (B : Finset (ZMod N)) :
    ∑ j : ZMod N, capCount width B j = width * B.card := by
  unfold capCount
  rw [Finset.sum_comm]
  have shift (k : ℕ) :
      (∑ j : ZMod N, if j + (k : ZMod N) ∈ B then 1 else 0) = B.card := by
    calc
      _ = ∑ j : ZMod N, if j ∈ B then 1 else 0 := by
        exact Equiv.sum_comp (Equiv.addRight (k : ZMod N))
          (fun j : ZMod N => if j ∈ B then (1 : ℕ) else 0)
      _ = B.card := by simp
  simp_rw [shift]
  simp

theorem exists_average {N : ℕ} [NeZero N] (width : ℕ)
    (B : Finset (ZMod N)) :
    ∃ j : ZMod N, width * B.card ≤ N * capCount width B j := by
  by_contra h
  push Not at h
  have hsum :
      (∑ j : ZMod N, N * capCount width B j) <
      ∑ _j : ZMod N, width * B.card := by
    apply Finset.sum_lt_sum_of_nonempty
    · exact Finset.univ_nonempty
    · intro j _
      exact h j
  rw [← Finset.mul_sum, cap_mass] at hsum
  simp only [Finset.sum_const, Finset.card_univ, ZMod.card, smul_eq_mul] at hsum
  omega

theorem odd_full_gain (m : ℕ) (hm : 1 ≤ m)
    (B : Finset (ZMod (2 * (2 * m + 1))))
    (hb : 2 * m - 1 ≤ B.card) :
    ∃ j, m ≤ capCount (2 * m) B j := by
  obtain ⟨j, hj⟩ := exists_average (2 * m) B
  refine ⟨j, ?_⟩
  have hlow : 2 * m * (2 * m - 1) ≤ 2 * m * B.card := Nat.mul_le_mul_left _ hb
  have hsub : 2 * m - 1 + 1 = 2 * m := by omega
  nlinarith

theorem even_full_gain (m : ℕ) (hm : 2 ≤ m)
    (B : Finset (ZMod (4 * m))) (hb : 2 * m - 1 ≤ B.card) :
    ∃ j, m ≤ capCount (2 * m - 1) B j := by
  letI : NeZero (4 * m) := ⟨by omega⟩
  obtain ⟨j, hj⟩ := exists_average (2 * m - 1) B
  refine ⟨j, ?_⟩
  have hlow := Nat.mul_le_mul_left (2 * m - 1) hb
  have hsub : 2 * m - 1 + 1 = 2 * m := by omega
  nlinarith

theorem odd_defect_two (m d b : ℕ) (hm : 1 ≤ m)
    (hboundary : 2 * m + 1 ≤ b + d) (hd : d ≤ 2) :
    2 * m - 1 ≤ b := by omega

theorem charging_bound (n b d bad : ℕ)
    (hendpoints : 2 * n = 2 * b + bad) (hcharge : bad ≤ 2 * d) :
    n ≤ b + d := by omega

theorem defect_extension_bound (n d : ℕ) (hn : 3 ≤ n)
    (B : Finset (ZMod (2 * n)))
    (hthree : 3 ≤ B.card) (hboundary : n ≤ B.card + d) :
    ∃ j, (n - 1) * max 3 (n - d) ≤ 2 * n * capCount (n - 1) B j := by
  letI : NeZero (2 * n) := ⟨by omega⟩
  obtain ⟨j, hj⟩ := exists_average (n - 1) B
  refine ⟨j, le_trans ?_ hj⟩
  apply Nat.mul_le_mul_left
  omega

theorem near_perfect_odd_extension (m d : ℕ) (hm : 1 ≤ m)
    (B : Finset (ZMod (2 * (2 * m + 1))))
    (hboundary : 2 * m + 1 ≤ B.card + d) (hd : d ≤ 2) :
    ∃ j, m ≤ capCount (2 * m) B j := by
  exact odd_full_gain m hm B (by omega)

/-- A statement only; no claim that this conjecture has been proved for K. -/
def FullStepClaim (K : ℕ → ℕ) : Prop :=
  ∀ n, 3 ≤ n → K n + n / 2 ≤ K (n + 1)

theorem full_step_iff_both_parities (K : ℕ → ℕ) :
    FullStepClaim K ↔
      (∀ m, 1 ≤ m → K (2*m+1) + m ≤ K (2*m+2)) ∧
      (∀ m, 2 ≤ m → K (2*m) + m ≤ K (2*m+1)) := by
  constructor
  · intro h
    constructor
    · intro m hm
      have := h (2*m+1) (by omega)
      convert this using 1; omega
    · intro m hm
      have := h (2*m) (by omega)
      convert this using 1; omega
  · rintro ⟨ho, he⟩ n hn
    by_cases hp : n % 2 = 0
    · have h := he (n/2) (by omega)
      have heq : 2*(n/2) = n := by omega
      simpa only [heq] using h
    · have h := ho (n/2) (by omega)
      have heq : 2*(n/2)+1 = n := by omega
      have heq2 : 2*(n/2)+2 = n+1 := by omega
      simpa only [heq, heq2] using h

#print axioms cap_mass
#print axioms exists_average
#print axioms odd_full_gain
#print axioms even_full_gain
#print axioms charging_bound
#print axioms defect_extension_bound
#print axioms near_perfect_odd_extension
#print axioms full_step_iff_both_parities

/-- The finite profile of the accompanying seven-line example. -/
theorem seven_profile_limited :
    ∀ j : ZMod 14, capCount 6 ({11, 5, 2} : Finset (ZMod 14)) j ≤ 2 := by
  decide +kernel

theorem seven_profile_attains_two :
    capCount 6 ({11, 5, 2} : Finset (ZMod 14)) 0 = 2 := by
  decide +kernel

#print axioms seven_profile_limited

end KobonBoundary
