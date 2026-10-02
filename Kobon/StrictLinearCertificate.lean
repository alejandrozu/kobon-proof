import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-! The elementary dual-certificate principle for strict affine systems.
This is classical linear programming soundness, not a new Kobon bound.
It supplies a small formal interface for the exact seed-fitting experiments;
those experiments' finite data and combinatorial coverage require separate
checks and are not asserted by this generic theorem. -/
namespace Kobon.StrictLinearCertificate
open Finset
open scoped BigOperators
set_option autoImplicit false

theorem weighted_evaluation {m d : Nat} (A : Fin m→Fin d→ℝ)
    (c w : Fin m→ℝ) (x : Fin d→ℝ) :
    (∑ i, w i*(c i+∑ j, A i j*x j)) =
      (∑ i, w i*c i)+∑ j, (∑ i, w i*A i j)*x j := by
  simp only [mul_add,sum_add_distrib,mul_sum,sum_mul,mul_assoc]
  rw [sum_comm]

/-- A nonzero nonnegative combination with zero variable coefficients and a
nonpositive constant excludes a solution of all strict inequalities. -/
theorem infeasible {m d : Nat} (A : Fin m→Fin d→ℝ)
    (c w : Fin m→ℝ)
    (hn : ∀ i, 0≤w i) (hp : ∃ i, 0<w i)
    (hzero : ∀ j, (∑ i, w i*A i j)=0)
    (hc : (∑ i, w i*c i)≤0) :
    ¬ ∃ x : Fin d→ℝ, ∀ i, 0<c i+∑ j, A i j*x j := by
  rintro ⟨x,hx⟩
  have hsum : 0<(∑ i, w i*(c i+∑ j, A i j*x j)) := by
    apply sum_pos'
    · intro i _
      exact mul_nonneg (hn i) (le_of_lt (hx i))
    · obtain ⟨i,hi⟩ := hp
      exact ⟨i,mem_univ _,mul_pos hi (hx i)⟩
  rw [weighted_evaluation] at hsum
  simp only [hzero,zero_mul,sum_const_zero,add_zero] at hsum
  exact (not_lt_of_ge hc) hsum

/-- The homogeneous form used by reciprocal-slope sign fitting. -/
theorem homogeneous_infeasible {m d : Nat} (A : Fin m→Fin d→ℝ)
    (w : Fin m→ℝ) (hn : ∀ i, 0≤w i) (hp : ∃ i, 0<w i)
    (hzero : ∀ j, (∑ i, w i*A i j)=0) :
    ¬ ∃ x : Fin d→ℝ, ∀ i, 0<∑ j, A i j*x j := by
  simpa using infeasible A (fun _ => 0) w hn hp hzero (by simp)

#print axioms infeasible
#print axioms homogeneous_infeasible
end Kobon.StrictLinearCertificate
