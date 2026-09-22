import Kobon.BBLAnalytic
import Kobon.BBLIntersection
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Tactic.FunProp

/-! The actual central maximum in the BBL rightmost old-line row.

The maximum is proved for the trigonometric pencil, then preserved under
small perturbations. No maximizing-index hypothesis is assumed.
-/
namespace Kobon.BBLCentral
open Real BBLAnalytic BBLMaximization BBLIntersection BBLExtrema Filter
open scoped Topology

noncomputable def g (r : Nat) (i : Fin (4*r)) (δ : ℝ) : ℝ :=
  sin (2*beta r i)+δ/tan (beta r i)
noncomputable def h (r : Nat) (i : Fin (4*r)) (δ : ℝ) : ℝ :=
  g r i δ*(1/tan (alpha r)-tan (beta r i))
noncomputable def corrected (r : Nat) (i : Fin (4*r)) (δ u : ℝ) : ℝ :=
  h r i δ/(1-u*g r i δ)

theorem leading_identity (a b : ℝ) (ha : sin a ≠ 0) (hb : cos b ≠ 0) :
    sin (2*b)*(1/tan a-tan b) = sin (2*b+a)/sin a-1 := by
  have hbt : sin (2*b)*tan b = 1-cos (2*b) := by
    rw [sin_two_mul,tan_eq_sin_div_cos,cos_two_mul]
    field_simp
    nlinarith [sin_sq_add_cos_sq b]
  rw [mul_sub,hbt,sin_add,tan_eq_sin_div_cos,one_div_div]
  field_simp
  <;> ring

theorem leading_formula (r : Nat) (hr : 5 ≤ r) (i : Fin (4*r)) :
    h r i 0 = sin (2*beta r i+alpha r)/sin (alpha r)-1 := by
  obtain ⟨ha,ha2,_⟩ := alpha_data r hr
  obtain ⟨hlo,hhi,_⟩ := beta_data r hr i
  have hsa : sin (alpha r) ≠ 0 := ne_of_gt (sin_pos_of_pos_of_lt_pi ha (by linarith))
  have hcb : cos (beta r i) ≠ 0 := ne_of_gt (cos_pos_of_mem_Ioo ⟨by linarith,by linarith⟩)
  simpa [h,g] using leading_identity (alpha r) (beta r i) hsa hcb

theorem leading_strict_maximum (r : Nat) (hr : 5 ≤ r) (c i : Fin (4*r))
    (hc : c.val+1 = 3*r) (hi : i ≠ c) : h r i 0 < h r c 0 := by
  obtain ⟨ha,ha2,hid⟩ := alpha_data r hr
  have hsa : 0 < sin (alpha r) := sin_pos_of_pos_of_lt_pi ha (by linarith)
  have hci : (c.val:ℝ)+1 = 3*(r:ℝ) := by exact_mod_cast hc
  have hac : 2*beta r c+alpha r = π/2 := by
    dsimp [beta]
    nlinarith
  have hia : i.val ≠ 3*r-1 := by
    intro hh
    apply hi
    apply Fin.ext
    omega
  have hs := sine_grid_separation r hr i hia
  have hai : 2*beta r i+alpha r = -π+((i.val:ℝ)+1)*(π/(2*(r:ℝ))) := by
    dsimp [beta,alpha]
    ring
  have hcos : cos (π/(2*(r:ℝ))) < 1 := by
    have hp : (0:ℝ) < r := by exact_mod_cast (show 0 < r by omega)
    have hx : 0 < π/(2*(r:ℝ)) := by positivity
    have hx2 : π/(2*(r:ℝ)) ≤ π := by
      apply (div_le_iff₀ (by positivity)).mpr
      have hR : (5:ℝ) ≤ r := by exact_mod_cast hr
      nlinarith [pi_pos]
    simpa using cos_lt_cos_of_nonneg_of_le_pi (le_refl (0:ℝ)) hx2 hx
  rw [leading_formula r hr i,leading_formula r hr c,hac,sin_pi_div_two]
  apply sub_lt_sub_right
  apply (div_lt_div_iff_of_pos_right hsa).2
  rw [hai]
  exact lt_of_le_of_lt hs hcos

/-- For each finite pencil size, a small δ preserves its actual central maximum. -/
theorem perturbed_strict_maximum (r : Nat) (hr : 5 ≤ r) (c : Fin (4*r))
    (hc : c.val+1 = 3*r) :
    ∀ᶠ δ in 𝓝 (0:ℝ), ∀ i : Fin (4*r), i ≠ c → h r i δ < h r c δ := by
  apply Filter.eventually_all.mpr
  intro i
  by_cases hi : i = c
  · exact Filter.Eventually.of_forall (fun _ hne => (hne hi).elim)
  have hf : ContinuousAt (h r i) 0 := by unfold h g; fun_prop
  have hg : ContinuousAt (h r c) 0 := by unfold h g; fun_prop
  exact (hf.eventually_lt hg (leading_strict_maximum r hr c i hc hi)).mono
    (fun _ hh _ => hh)

/-- After choosing δ, a sufficiently small positive scale-to-old-slope ratio u
preserves the maximum for the exact rational intersection expression. -/
theorem corrected_strict_maximum (r : Nat) (c : Fin (4*r)) (δ : ℝ)
    (hmax : ∀ i : Fin (4*r), i ≠ c → h r i δ < h r c δ) :
    ∀ᶠ u in 𝓝 (0:ℝ), ∀ i : Fin (4*r), i ≠ c →
      corrected r i δ u < corrected r c δ u := by
  apply Filter.eventually_all.mpr
  intro i
  by_cases hi : i = c
  · exact Filter.Eventually.of_forall (fun _ hne => (hne hi).elim)
  have hf : ContinuousAt (corrected r i δ) 0 := by
    unfold corrected
    fun_prop (disch := norm_num)
  have hg : ContinuousAt (corrected r c δ) 0 := by
    unfold corrected
    fun_prop (disch := norm_num)
  have hh : corrected r i δ 0 < corrected r c δ 0 := by
    simpa [corrected] using hmax i hi
  exact (hf.eventually_lt hg hh).mono (fun _ hh _ => hh)

/-- The normalized rational expression is the actual old-new x coordinate. -/
theorem rightmost_crossing_x (r : Nat) (i : Fin (4*r)) (δ u m : ℝ)
    (hm : m ≠ 0) (hd : 1-u*g r i δ ≠ 0) :
    (intersection (graphLine m (1/tan (alpha r)))
      (graphLine (m*u*g r i δ) (tan (beta r i)))).1 =
      1/tan (alpha r)+u*corrected r i δ u := by
  have hms : m ≠ m*u*g r i δ := by
    intro hh
    have hp : m*(1-u*g r i δ) = 0 := by nlinarith only [hh]
    exact hd ((mul_eq_zero.mp hp).resolve_left hm)
  rw [graph_crossing_x _ _ _ _ hms]
  unfold corrected h
  field_simp
  <;> ring

/-- For the actual lines, the central added line meets the rightmost old line
strictly to the right of every other added line, at sufficiently small scale. -/
theorem rightmost_central_maximum (r : Nat) (c : Fin (4*r)) (δ m : ℝ)
    (hm : m ≠ 0)
    (hmax : ∀ i : Fin (4*r), i ≠ c → h r i δ < h r c δ) :
    ∀ᶠ u in 𝓝 (0:ℝ), 0 < u → ∀ i : Fin (4*r), i ≠ c →
      (intersection (graphLine m (1/tan (alpha r)))
        (graphLine (m*u*g r i δ) (tan (beta r i)))).1 <
      (intersection (graphLine m (1/tan (alpha r)))
        (graphLine (m*u*g r c δ) (tan (beta r c)))).1 := by
  have hd : ∀ᶠ u in 𝓝 (0:ℝ), ∀ i : Fin (4*r), 0 < 1-u*g r i δ := by
    apply Filter.eventually_all.mpr
    intro i
    have hf : ContinuousAt (fun u : ℝ => 1-u*g r i δ) 0 := by fun_prop
    exact Filter.Tendsto.eventually_const_lt (by norm_num : (0:ℝ) < 1-0*g r i δ) hf
  have hc := corrected_strict_maximum r c δ hmax
  apply (hd.and hc).mono
  intro u hu hup i hic
  rw [rightmost_crossing_x r i δ u m hm (ne_of_gt (hu.1 i)),
    rightmost_crossing_x r c δ u m hm (ne_of_gt (hu.1 c))]
  linarith [mul_lt_mul_of_pos_left (hu.2 i hic) hup]

/-- All ingredients determining the maximizing line are proved here; the
remaining geometric induction needs only realize the other crossing rows. -/
theorem eventual_rightmost_central_maximum (r : Nat) (hr : 5 ≤ r)
    (c : Fin (4*r)) (hc : c.val+1 = 3*r) (m : ℝ) (hm : m ≠ 0) :
    ∀ᶠ δ in 𝓝 (0:ℝ), ∀ᶠ u in 𝓝 (0:ℝ), 0 < u →
      ∀ i : Fin (4*r), i ≠ c →
      (intersection (graphLine m (1/tan (alpha r)))
        (graphLine (m*u*g r i δ) (tan (beta r i)))).1 <
      (intersection (graphLine m (1/tan (alpha r)))
        (graphLine (m*u*g r c δ) (tan (beta r c)))).1 := by
  exact (perturbed_strict_maximum r hr c hc).mono
    (fun δ hδ => rightmost_central_maximum r c δ m hm hδ)

#print axioms perturbed_strict_maximum
#print axioms corrected_strict_maximum
#print axioms eventual_rightmost_central_maximum
end Kobon.BBLCentral
