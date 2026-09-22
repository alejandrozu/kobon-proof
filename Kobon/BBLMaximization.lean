import Kobon.BBLTangentBounds

/-! Quantitative discrete trigonometric separation and stable rational maxima.
These are analytic components of the BBL right-boundary induction, not a
substitute for the remaining complete arrangement/doubling formalization.
-/
namespace Kobon.BBLMaximization
open Real

theorem sine_grid_separation (r : Nat) (hr : 5≤r) (i : Fin (4*r))
    (hi : i.val ≠ 3*r-1) :
    sin (-π+((i.val:ℝ)+1)*(π/(2*(r:ℝ)))) ≤ cos (π/(2*(r:ℝ))) := by
  let R : ℝ := r
  let s : ℝ := π/(2*R)
  let z : ℝ := -π+((i.val:ℝ)+1)*s
  have hR : 5≤R := by dsimp [R]; exact_mod_cast hr
  have hRp : 0<R := by linarith
  have hs : 0<s := div_pos pi_pos (by positivity)
  have hden : 2*R*s=π := by
    dsimp [s]
    field_simp
  have hs2 : s<π/2 := by nlinarith
  have hiv : (i.val:ℝ)+1≤4*R := by
    have hn : i.val+1≤4*r := i.isLt
    dsimp [R]
    exact_mod_cast hn
  have hiz : 0≤(i.val:ℝ)+1 := by positivity
  have hzlo : -π≤z := by
    dsimp [z]
    linarith [mul_nonneg hiz (le_of_lt hs)]
  have hzhi : z≤π := by
    have hm := mul_le_mul_of_nonneg_right hiv (le_of_lt hs)
    dsimp [z]
    nlinarith
  have hcos : 0≤cos s := cos_nonneg_of_mem_Icc (by constructor <;> linarith [pi_pos])
  change sin z≤cos s
  by_cases hzneg : z≤0
  · exact le_trans (sin_nonpos_of_nonpos_of_neg_pi_le hzneg hzlo) hcos
  have hzpos : 0<z := lt_of_not_ge hzneg
  have hineq : i.val+1 ≠ 3*r := by omega
  rcases lt_or_gt_of_ne hineq with hlow | hhigh
  · have hgap : (i.val:ℝ)+2≤3*R := by
      have hn : i.val+2≤3*r := by omega
      dsimp [R]
      exact_mod_cast hn
    have hm := mul_le_mul_of_nonneg_right hgap (le_of_lt hs)
    have hz : z≤π/2-s := by dsimp [z]; nlinarith
    have hsin := sin_le_sin_of_le_of_le_pi_div_two
      (show -(π/2)≤z by linarith [pi_pos])
      (show π/2-s≤π/2 by linarith) hz
    simpa only [sin_pi_div_two_sub] using hsin
  · have hgap : 3*R≤(i.val:ℝ) := by
      have hn : 3*r ≤ i.val := by omega
      dsimp [R]
      exact_mod_cast hn
    have hm := mul_le_mul_of_nonneg_right hgap (le_of_lt hs)
    have hz : π/2+s≤z := by dsimp [z]; nlinarith
    have hsin := sin_le_sin_of_le_of_le_pi_div_two
      (show -(π/2)≤π-z by linarith [pi_pos])
      (show π/2-s≤π/2 by linarith)
      (show π-z≤π/2-s by linarith)
    simpa only [sin_pi_sub,sin_pi_div_two_sub] using hsin

theorem rational_error_bound (h z : ℝ) (hz : |z| ≤ 1/2) :
    |h/(1-z)-h| ≤ 2 * |h| * |z| := by
  have hz' : z≤1/2 := le_trans (le_abs_self z) hz
  have hd : 0<1-z := by linarith
  have heq : h/(1-z)-h=h*z/(1-z) := by field_simp; ring
  rw [heq,abs_div,abs_mul,abs_of_pos hd]
  apply (div_le_iff₀ hd).mpr
  have hp := mul_nonneg (mul_nonneg (abs_nonneg h) (abs_nonneg z))
    (show 0≤1-2*z by linarith)
  nlinarith

/-- The central index remains the unique maximizer under certified perturbations.
This is an ordinary real inequality; it does not assume the desired ordering. -/
theorem stable_maximum (Hc Ho hc ho zc zo gap err size zbound : ℝ)
    (hgap : gap≤Hc-Ho) (hec : |hc-Hc|≤err) (heo : |ho-Ho|≤err)
    (hhc : |hc|≤size) (hho : |ho|≤size)
    (hzc : |zc|≤zbound) (hzo : |zo|≤zbound) (hz : zbound≤1/2)
    (hsmall : 2*err+4*size*zbound<gap) :
    ho/(1-zo)<hc/(1-zc) := by
  have hcerror := rational_error_bound hc zc (le_trans hzc hz)
  have hoerror := rational_error_bound ho zo (le_trans hzo hz)
  have hs : 0≤size := le_trans (abs_nonneg hc) hhc
  have hzb : 0≤zbound := le_trans (abs_nonneg zc) hzc
  have ec : |hc/(1-zc)-hc|≤2*size*zbound := by
    apply le_trans hcerror
    exact mul_le_mul (mul_le_mul_of_nonneg_left hhc (by norm_num)) hzc
      (abs_nonneg zc) (by positivity)
  have eo : |ho/(1-zo)-ho|≤2*size*zbound := by
    apply le_trans hoerror
    exact mul_le_mul (mul_le_mul_of_nonneg_left hho (by norm_num)) hzo
      (abs_nonneg zo) (by positivity)
  obtain ⟨ec1,ec2⟩ := abs_le.mp ec
  obtain ⟨eo1,eo2⟩ := abs_le.mp eo
  obtain ⟨hec1,hec2⟩ := abs_le.mp hec
  obtain ⟨heo1,heo2⟩ := abs_le.mp heo
  linarith

#print axioms sine_grid_separation
#print axioms stable_maximum
end Kobon.BBLMaximization
