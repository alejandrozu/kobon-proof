import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

/-!
# Conditional arithmetic for the multiple-point core

This file proves arithmetic implications of explicitly supplied incidence and
parity budgets. It does not formalize elementary arrangement edges, prove the
geometric charging lemma, or give an unconditional upper bound for Kobon
arrangements. The paper-level geometric derivation and its limitations are in
`research/six-hour-2026-09-21/general-bounds/clean-line-parity.md`.
-/

namespace Kobon.CleanLineBudget

/-- Incidence identity plus the clean-line charging inequality. Every premise
is explicit; `P`, `S`, `U`, `D₁`, `D₂`, and `h` are abstract integer counts. -/
theorem parity_budget
    (n P S U D₁ D₂ h δ : ℤ)
    (incidence : δ = 2 * P + S + U - D₁ - D₂)
    (charging : n - h ≤ 2 * U + D₁ + 2 * P) :
    n + 2 * P + 2 * S - h - 3 * D₁ - 2 * D₂ ≤ 2 * δ := by
  omega

/-- Arithmetic consequence when all finite multiple points are triple and
there are at most two of them. The fan and core bounds are assumptions here. -/
theorem at_most_two_triple_points
    (m P U D₁ D₂ h q δ : ℤ)
    (parallel_nonneg : 0 ≤ P)
    (triple_nonneg : 0 ≤ q) (triple_le_two : q ≤ 2)
    (incidence : δ = 2 * P + 3 * q + U - D₁ - D₂)
    (charging : 2 * m - h ≤ 2 * U + D₁ + 2 * P)
    (fan : D₁ ≤ 2 * q)
    (core : h ≤ 3 * q - D₂)
    (core_edges : D₂ ≤ 1) :
    m - 3 ≤ δ := by
  omega

/-- With a single finite triple point there is no shared core-to-core edge. -/
theorem one_triple_point
    (m P U D₁ h δ : ℤ)
    (parallel_nonneg : 0 ≤ P)
    (incidence : δ = 2 * P + 3 + U - D₁)
    (charging : 2 * m - h ≤ 2 * U + D₁ + 2 * P)
    (fan : D₁ ≤ 2) (core : h ≤ 3) :
    m - 1 ≤ δ := by
  omega

/-- Higher multiplicity improves the local weighted budget. -/
theorem multiplicity_surplus (r : ℤ) (hr : 3 ≤ r) :
    0 ≤ 2 * (r * (r - 2)) - 7 * r + 15 := by
  have hprod : 0 ≤ (r - 3) * (2 * r - 5) := mul_nonneg (by omega) (by omega)
  nlinarith

/-- Generalization to at most two multiple points of arbitrary multiplicity.
`I` is their total line-incidence count; the weighted surplus follows by
summing `multiplicity_surplus`. All geometric premises remain explicit. -/
theorem at_most_two_multiple_points
    (m S I U D₁ D₂ h q δ : ℤ)
    (triple_nonneg : 0 ≤ q) (points_le_two : q ≤ 2)
    (incidence : δ = S + U - D₁ - D₂)
    (charging : 2 * m - h ≤ 2 * U + D₁)
    (fan : D₁ ≤ 2 * I - 4 * q)
    (core : h ≤ I - D₂)
    (core_edges : D₂ ≤ 1)
    (surplus : 0 ≤ 2 * S - 7 * I + 15 * q) :
    m - 3 ≤ δ := by
  omega

/-- General fan inequality: D1 counts ordinary-endpoint shared segments,
I is total multiple-point incidence, and q is the number of multiple points.
The local ray bound and total-ray count remain explicit premises. -/
theorem general_multiplicity_budget
    (n S I U D₁ D₂ h q δ : ℤ)
    (incidence : δ = S+U-D₁-D₂)
    (charging : n-h≤2*U+D₁)
    (core_incidence : h≤I)
    (fan_runs : D₁≤2*I-3*q)
    (fan_rays : D₁+2*D₂≤2*I) :
    n+2*S-7*I+6*q≤2*δ := by
  omega

/-- A point of multiplicity at least five has positive weight in the general
fan budget; the factorization is 1+(r-5)(2r-1). -/
theorem high_multiplicity_weight (r : ℤ) (hr : 5≤r) :
    1≤2*r*(r-2)-7*r+6 := by
  have hp : 0≤(r-5)*(2*r-1) := mul_nonneg (by omega) (by omega)
  nlinarith

/-- Explicit arithmetic consequence of a nonnegative total local weight.
The application to Euclidean arrangements still needs the geometric budgets. -/
theorem nonnegative_core_weight
    (n S I U D₁ D₂ h q δ : ℤ)
    (incidence : δ = S+U-D₁-D₂)
    (charging : n-h≤2*U+D₁)
    (core_incidence : h≤I)
    (fan_runs : D₁≤2*I-3*q)
    (fan_rays : D₁+2*D₂≤2*I)
    (weight : 0≤2*S-7*I+6*q) : n≤2*δ := by
  have hh := general_multiplicity_budget n S I U D₁ D₂ h q δ
    incidence charging core_incidence fan_runs fan_rays
  omega

/-- The resulting upper inequality, still conditional on the supplied defect
bound. The even number of lines is represented by `2*m`. -/
theorem triangles_from_defect
    (m T δ : ℤ)
    (definition : δ = (2 * m) * (2 * m - 2) - 3 * T)
    (defect : m - 3 ≤ δ) :
    3 * T ≤ (2 * m) * (2 * m - 2) - m + 3 := by
  linarith

end Kobon.CleanLineBudget
