import Kobon.BBLExtrema
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-! Exact algebra behind the BBL near-horizontal pencil.
Writing the intercept as `t = tan β` avoids trigonometry in the crossing
formula. All identities below concern actual affine lines over the reals.
-/
namespace Kobon.BBLIntersection
open BBLExtrema Exterior

noncomputable def slopeFactor (δ t : ℝ) : ℝ := 2*t/(1+t^2)+δ/t
noncomputable def pencilLine (κ δ t : ℝ) : Line ℝ := graphLine (κ*slopeFactor δ t) t
noncomputable def pairDen (δ t u : ℝ) : ℝ :=
  2*t*u*(1-t*u)-δ*(1+t^2)*(1+u^2)

theorem one_add_sq_pos (t : ℝ) : 0 < 1+t^2 := by nlinarith [sq_nonneg t]

theorem factor_difference (δ t u : ℝ) (ht : t ≠ 0) (hu : u ≠ 0) :
    slopeFactor δ t-slopeFactor δ u =
      (t-u)*pairDen δ t u/(t*u*(1+t^2)*(1+u^2)) := by
  unfold slopeFactor pairDen
  field_simp [ht,hu,ne_of_gt (one_add_sq_pos t),ne_of_gt (one_add_sq_pos u)]
  <;> ring

theorem weighted_factor_difference (δ t u : ℝ) (ht : t ≠ 0) (hu : u ≠ 0) :
    slopeFactor δ t*t-slopeFactor δ u*u =
      2*(t-u)*(t+u)/((1+t^2)*(1+u^2)) := by
  unfold slopeFactor
  field_simp [ht,hu,ne_of_gt (one_add_sq_pos t),ne_of_gt (one_add_sq_pos u)]
  <;> ring

theorem pencil_no_parallel (κ δ t u : ℝ) (hκ : κ ≠ 0)
    (ht : t ≠ 0) (hu : u ≠ 0) (htu : t ≠ u) (hd : pairDen δ t u ≠ 0) :
    det (pencilLine κ δ t) (pencilLine κ δ u) ≠ 0 := by
  have hf : slopeFactor δ t-slopeFactor δ u ≠ 0 := by
    rw [factor_difference δ t u ht hu]
    exact div_ne_zero (mul_ne_zero (sub_ne_zero.mpr htu) hd)
      (by exact mul_ne_zero (mul_ne_zero (mul_ne_zero ht hu)
        (ne_of_gt (one_add_sq_pos t))) (ne_of_gt (one_add_sq_pos u)))
  have heq : det (pencilLine κ δ t) (pencilLine κ δ u) =
      -κ*(slopeFactor δ t-slopeFactor δ u) := by
    dsimp [det,pencilLine,graphLine]; ring
  rw [heq]
  exact mul_ne_zero (neg_ne_zero.mpr hκ) hf

theorem graph_crossing_x (m a s b : ℝ) (hms : m ≠ s) :
    (intersection (graphLine m a) (graphLine s b)).1 = (m*a-s*b)/(m-s) := by
  dsimp [intersection,vertex,det,graphLine]
  rw [show m*a*(-1)-(-1)*(s*b) = -(m*a-s*b) by ring,
    show m*(-1)-(-1)*s = -(m-s) by ring]
  field_simp [sub_ne_zero.mpr hms,sub_ne_zero.mpr (Ne.symm hms)]
  <;> ring

/-- New-new crossing coordinates are independent of the common small scale κ. -/
theorem pencil_crossing_x (κ δ t u : ℝ) (hκ : κ ≠ 0)
    (ht : t ≠ 0) (hu : u ≠ 0) (htu : t ≠ u) (hd : pairDen δ t u ≠ 0) :
    (intersection (pencilLine κ δ t) (pencilLine κ δ u)).1 =
      2*t*u*(t+u)/pairDen δ t u := by
  have hf : slopeFactor δ t-slopeFactor δ u ≠ 0 := by
    rw [factor_difference δ t u ht hu]
    exact div_ne_zero (mul_ne_zero (sub_ne_zero.mpr htu) hd)
      (by exact mul_ne_zero (mul_ne_zero (mul_ne_zero ht hu)
        (ne_of_gt (one_add_sq_pos t))) (ne_of_gt (one_add_sq_pos u)))
  have hms : κ*slopeFactor δ t ≠ κ*slopeFactor δ u := by
    intro hh; exact hf (sub_eq_zero.mpr (mul_left_cancel₀ hκ hh))
  rw [pencilLine,pencilLine,graph_crossing_x _ _ _ _ hms]
  have heq : (κ*slopeFactor δ t*t-κ*slopeFactor δ u*u)/
      (κ*slopeFactor δ t-κ*slopeFactor δ u) =
      (slopeFactor δ t*t-slopeFactor δ u*u)/(slopeFactor δ t-slopeFactor δ u) := by
    field_simp
    <;> ring
  rw [heq,weighted_factor_difference δ t u ht hu,factor_difference δ t u ht hu]
  field_simp [ht,hu,sub_ne_zero.mpr htu,hd,
    ne_of_gt (one_add_sq_pos t),ne_of_gt (one_add_sq_pos u)]
  <;> ring

/-- Displacement from the unperturbed tangent-sum crossing. -/
theorem crossing_displacement (δ t u : ℝ) (hd : pairDen δ t u ≠ 0)
    (hc : 1-t*u ≠ 0) :
    2*t*u*(t+u)/pairDen δ t u-(t+u)/(1-t*u) =
      δ*(t+u)*(1+t^2)*(1+u^2)/(pairDen δ t u*(1-t*u)) := by
  unfold pairDen at *
  field_simp
  <;> ring

/-- Exceptional complementary negative or positive pairs lie far outside:
their coordinate has exact reciprocal dependence on δ. -/
theorem complementary_crossing (δ t u : ℝ) (hprod : t*u = 1) :
    2*t*u*(t+u)/pairDen δ t u =
      -2*(t+u)/(δ*(1+t^2)*(1+u^2)) := by
  have hd : pairDen δ t u = -(δ*(1+t^2)*(1+u^2)) := by
    unfold pairDen
    rw [hprod]
    ring
  have hn : 2*t*u*(t+u) = 2*(t+u) := by
    calc
      _ = 2*(t*u)*(t+u) := by ring
      _ = _ := by rw [hprod]; ring
  rw [hd,hn,div_neg]
  ring

#print axioms pencil_crossing_x
#print axioms crossing_displacement
end Kobon.BBLIntersection


