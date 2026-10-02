import Kobon.CleanLineBudget
import Kobon.UpperFan
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

/-!
# Improved conditional budgets for small multiple-point cores

The new geometric local theorem in `UpperFan` supplies d1<=2r-4 when at
most two shared rays end at another core point. Thus it applies locally to
arrangements with at most three core points, rather than only two.

This module checks the aggregate arithmetic. Incidence, clean-line charging,
core extraction and summation hypotheses remain explicit. These declarations
must not be described as complete Lean upper theorems for arbitrary line
arrangements.
-/
namespace Kobon.UpperCoreBudget
open Finset
open scoped BigOperators

/-- Sum the strengthened weighted local fan inequalities. -/
theorem sum_local_fan_bound {α : Type*} [Fintype α]
    (r d₁ d₂ e : α → ℤ)
    (local_bound : ∀ v, 3*d₁ v+d₂ v≤6*r v-8+2*e v) :
    3*(∑ v, d₁ v)+(∑ v, d₂ v)≤
      6*(∑ v, r v)-8*Fintype.card α+2*(∑ v, e v) := by
  have h := sum_le_sum (s:=univ) (fun v _ => local_bound v)
  simp only [sum_add_distrib,sum_sub_distrib,sum_const,
    ← mul_sum,nsmul_eq_mul,card_univ] at h
  nlinarith [h]

/-- Global conditional refinement, retaining the number e of exceptional
full fans. The inequality improves the older weighted budget by 2(q-e). -/
theorem weighted_defect
    (n S I U D₁ D₂ h q e δ : ℤ)
    (incidence : δ=S+U-D₁-D₂)
    (charging : n-h≤2*U+D₁)
    (core : h≤I)
    (fan : 3*D₁+2*D₂≤6*I-8*q+2*e) :
    n+2*S-7*I+8*q-2*e≤2*δ := by
  omega

/-- Counting each used core-to-core segment against the repeated incidence
of its supporting line yields a further D2 term, when that geometric count
has been supplied. -/
theorem weighted_defect_with_core_edges
    (n S I U D₁ D₂ h q e δ : ℤ)
    (incidence : δ=S+U-D₁-D₂)
    (charging : n-h≤2*U+D₁)
    (core : h≤I-D₂)
    (fan : 3*D₁+2*D₂≤6*I-8*q+2*e) :
    n+2*S-7*I+8*q-2*e+D₂≤2*δ := by
  omega

/-- The new local <=2 theorem extends the small-core budget to q<=3.
The bounds on shared rays and core edges are explicit geometric premises. -/
theorem at_most_three_multiple_points
    (m S I U D₁ D₂ h q δ : ℤ)
    (points_nonneg : 0≤q) (points_le_three : q≤3)
    (incidence : δ=S+U-D₁-D₂)
    (charging : 2*m-h≤2*U+D₁)
    (fan : D₁≤2*I-4*q)
    (core : h≤I-D₂)
    (core_edges : D₂≤3)
    (surplus : 0≤2*S-7*I+15*q) :
    m-6≤δ := by
  omega

/-- Restricted upper polynomial plus two, conditional on the defect
conclusion. Integer division is floor division. -/
theorem triangles_from_three_core_defect
    (m T δ : ℤ)
    (definition : δ=(2*m)*(2*m-2)-3*T)
    (defect : m-6≤δ) :
    T≤m*(4*m-5)/3+2 := by
  have he : (2*m)*(2*m-2)-m=m*(4*m-5) := by ring
  have hh : 3*(T-2)≤m*(4*m-5) := by nlinarith
  omega

#print axioms weighted_defect
#print axioms at_most_three_multiple_points
#print axioms triangles_from_three_core_defect
end Kobon.UpperCoreBudget



