import Kobon.BBLGrid
import Kobon.BBLPersistence

/-! Qualitative crossing limits for the BBL pencil.
These prove the strict displacement of the new-new intersections from the
old tangent grid; a later, smaller κ separates old-new intersections from them.
-/
namespace Kobon.BBLPencilLimits
open BBLIntersection BBLExtrema BBLPersistence Filter
open scoped Topology

noncomputable def pairX (δ t u : ℝ) : ℝ := 2*t*u*(t+u)/pairDen δ t u
noncomputable def displacementCoeff (δ t u : ℝ) : ℝ :=
  (t+u)*(1+t^2)*(1+u^2)/(pairDen δ t u*(1-t*u))

theorem pairDen_zero (t u : ℝ) : pairDen 0 t u = 2*t*u*(1-t*u) := by
  simp [pairDen]

theorem pairDen_zero_ne (t u : ℝ) (ht : t ≠ 0) (hu : u ≠ 0)
    (hc : 1-t*u ≠ 0) : pairDen 0 t u ≠ 0 := by
  rw [pairDen_zero]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) ht) hu) hc

theorem pairX_zero (t u : ℝ) (ht : t ≠ 0) (hu : u ≠ 0)
    (hc : 1-t*u ≠ 0) : pairX 0 t u = (t+u)/(1-t*u) := by
  unfold pairX
  rw [pairDen_zero]
  field_simp
  <;> ring

theorem pairX_continuousAt_zero (t u : ℝ) (ht : t ≠ 0) (hu : u ≠ 0)
    (hc : 1-t*u ≠ 0) : ContinuousAt (fun δ => pairX δ t u) 0 := by
  unfold pairX
  apply ContinuousAt.div continuousAt_const
  · unfold pairDen
    fun_prop
  · exact pairDen_zero_ne t u ht hu hc

theorem pairX_tendsto (t u : ℝ) (ht : t ≠ 0) (hu : u ≠ 0)
    (hc : 1-t*u ≠ 0) :
    Tendsto (fun δ => pairX δ t u) (𝓝 0) (𝓝 ((t+u)/(1-t*u))) := by
  have hh : Tendsto (fun δ => pairX δ t u) (𝓝 0) (𝓝 (pairX 0 t u)) :=
    pairX_continuousAt_zero t u ht hu hc
  rw [pairX_zero t u ht hu hc] at hh
  exact hh

theorem displacementCoeff_continuousAt_zero (t u : ℝ) (ht : t ≠ 0) (hu : u ≠ 0)
    (hc : 1-t*u ≠ 0) : ContinuousAt (fun δ => displacementCoeff δ t u) 0 := by
  unfold displacementCoeff
  apply ContinuousAt.div continuousAt_const
  · unfold pairDen
    fun_prop
  · exact mul_ne_zero (pairDen_zero_ne t u ht hu hc) hc

theorem displacementCoeff_zero (t u : ℝ) (ht : t ≠ 0) (hu : u ≠ 0)
    (hc : 1-t*u ≠ 0) : displacementCoeff 0 t u =
      ((t+u)*(t*u)*(1+t^2)*(1+u^2))/(2*(t*u)^2*(1-t*u)^2) := by
  unfold displacementCoeff
  rw [pairDen_zero]
  field_simp
  <;> ring

theorem displacementCoeff_zero_pos (t u : ℝ) (ht : t ≠ 0) (hu : u ≠ 0)
    (hc : 1-t*u ≠ 0) (hs : 0 < (t+u)*(t*u)) : 0 < displacementCoeff 0 t u := by
  rw [displacementCoeff_zero t u ht hu hc]
  apply div_pos
  · exact mul_pos (mul_pos hs (one_add_sq_pos t)) (one_add_sq_pos u)
  · exact mul_pos (mul_pos (by norm_num) (sq_pos_of_ne_zero (mul_ne_zero ht hu)))
      (sq_pos_of_ne_zero hc)

theorem displacementCoeff_zero_neg (t u : ℝ) (ht : t ≠ 0) (hu : u ≠ 0)
    (hc : 1-t*u ≠ 0) (hs : (t+u)*(t*u) < 0) : displacementCoeff 0 t u < 0 := by
  rw [displacementCoeff_zero t u ht hu hc]
  apply div_neg_of_neg_of_pos
  · exact mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos hs (one_add_sq_pos t))
      (one_add_sq_pos u)
  · exact mul_pos (mul_pos (by norm_num) (sq_pos_of_ne_zero (mul_ne_zero ht hu)))
      (sq_pos_of_ne_zero hc)

theorem displacement_identity (δ t u : ℝ) (hd : pairDen δ t u ≠ 0)
    (hc : 1-t*u ≠ 0) : pairX δ t u-(t+u)/(1-t*u) = δ*displacementCoeff δ t u := by
  rw [pairX,crossing_displacement δ t u hd hc]
  unfold displacementCoeff
  ring

/-- For small positive δ, the crossing shifts right exactly in the positive
algebraic sign case. The bound comes from actual rational line intersections. -/
theorem crossing_right_eventually (t u : ℝ) (ht : t ≠ 0) (hu : u ≠ 0)
    (hc : 1-t*u ≠ 0) (hs : 0 < (t+u)*(t*u)) :
    ∀ᶠ δ in 𝓝 (0:ℝ), 0 < δ → (t+u)/(1-t*u) < pairX δ t u := by
  have hcont := displacementCoeff_continuousAt_zero t u ht hu hc
  have hpos := Filter.Tendsto.eventually_const_lt (displacementCoeff_zero_pos t u ht hu hc hs) hcont
  apply hpos.mono
  intro δ hδ hδpos
  have hd : pairDen δ t u ≠ 0 := by
    intro hz
    simp [displacementCoeff,hz] at hδ
  have heq := displacement_identity δ t u hd hc
  have hp := mul_pos hδpos hδ
  linarith

theorem crossing_left_eventually (t u : ℝ) (ht : t ≠ 0) (hu : u ≠ 0)
    (hc : 1-t*u ≠ 0) (hs : (t+u)*(t*u) < 0) :
    ∀ᶠ δ in 𝓝 (0:ℝ), 0 < δ → pairX δ t u < (t+u)/(1-t*u) := by
  have hcont := displacementCoeff_continuousAt_zero t u ht hu hc
  have hneg := Filter.Tendsto.eventually_lt_const (displacementCoeff_zero_neg t u ht hu hc hs) hcont
  apply hneg.mono
  intro δ hδ hδpos
  have hd : pairDen δ t u ≠ 0 := by
    intro hz
    simp [displacementCoeff,hz] at hδ
  have heq := displacement_identity δ t u hd hc
  have hp := mul_neg_of_pos_of_neg hδpos hδ
  linarith

/-- An old-new crossing tends to the old intercept as the pencil scale shrinks. -/
theorem old_new_crossing_tendsto (m a v b : ℝ) (hm : m ≠ 0) :
    Tendsto (fun κ => (intersection (graphLine m a) (graphLine (κ*v) b)).1)
      (𝓝 0) (𝓝 a) := by
  have hc : ContinuousAt (fun κ : ℝ => (m*a-κ*v*b)/(m-κ*v)) 0 := by
    fun_prop (disch := simpa using hm)
  have heq : (fun κ : ℝ => (intersection (graphLine m a) (graphLine (κ*v) b)).1) =ᶠ[𝓝 0]
      (fun κ : ℝ => (m*a-κ*v*b)/(m-κ*v)) := by
    have hd : ∀ᶠ κ in 𝓝 (0:ℝ), m-κ*v ≠ 0 := by
      have hcont : ContinuousAt (fun κ : ℝ => m-κ*v) 0 := by fun_prop
      exact hcont.eventually_ne (by simpa using hm)
    apply hd.mono
    intro κ hκ
    exact graph_crossing_x _ _ _ _ (sub_ne_zero.mp hκ)
  have hct : Tendsto (fun κ : ℝ => (m*a-κ*v*b)/(m-κ*v))
      (𝓝 0) (𝓝 ((m*a-0*v*b)/(m-0*v))) := hc
  have hval : (m*a-0*v*b)/(m-0*v) = a := by simp [hm]
  rw [hval] at hct
  exact hct.congr' heq.symm

theorem complementary_pairX (δ t u : ℝ) (hp : t*u = 1) :
    pairX δ t u = (-2*(t+u)/((1+t^2)*(1+u^2)))/δ := by
  rw [pairX,complementary_crossing δ t u hp]
  rw [div_div]
  congr 1
  ring

theorem positive_over_small (C A : ℝ) (hC : 0 < C) :
    ∀ᶠ δ in 𝓝 (0:ℝ), 0 < δ → A < C/δ := by
  have hc : ContinuousAt (fun δ : ℝ => δ*(|A|+1)) 0 := by fun_prop
  have he := Filter.Tendsto.eventually_lt_const (by simpa using hC : (0:ℝ)*(|A|+1) < C) hc
  apply he.mono
  intro δ hδ hδp
  apply (lt_div_iff₀ hδp).mpr
  have ha : A < |A|+1 := by linarith [le_abs_self A]
  have hm := mul_lt_mul_of_pos_right ha hδp
  nlinarith

theorem complementary_far_right (t u A : ℝ) (hp : t*u = 1) (hs : t+u < 0) :
    ∀ᶠ δ in 𝓝 (0:ℝ), 0 < δ → A < pairX δ t u := by
  have hC : 0 < -2*(t+u)/((1+t^2)*(1+u^2)) := by
    apply div_pos
    · nlinarith
    · exact mul_pos (one_add_sq_pos t) (one_add_sq_pos u)
  exact (positive_over_small _ A hC).mono (fun δ hδ hδp => by
    rw [complementary_pairX δ t u hp]
    exact hδ hδp)

theorem complementary_far_left (t u A : ℝ) (hp : t*u = 1) (hs : 0 < t+u) :
    ∀ᶠ δ in 𝓝 (0:ℝ), 0 < δ → pairX δ t u < A := by
  have hC : 0 < 2*(t+u)/((1+t^2)*(1+u^2)) := by
    apply div_pos
    · positivity
    · exact mul_pos (one_add_sq_pos t) (one_add_sq_pos u)
  apply (positive_over_small _ (-A) hC).mono
  intro δ hδ hδp
  have hh := hδ hδp
  rw [complementary_pairX δ t u hp]
  have hid : (-2*(t+u)/((1+t^2)*(1+u^2)))/δ =
      -(2*(t+u)/((1+t^2)*(1+u^2))/δ) := by ring
  rw [hid]
  linarith

#print axioms crossing_right_eventually
#print axioms crossing_left_eventually
#print axioms old_new_crossing_tendsto
end Kobon.BBLPencilLimits
