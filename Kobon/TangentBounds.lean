import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Exact rational enclosures for the four actual tangent constants of the seed.
These use trigonometric identities and the algebraic value of cos(pi/5),
not a floating-point oracle or an assumed interval calculation. -/
namespace Kobon.TangentBounds
open Real

theorem sqrt_five_bounds : (2236067:ℝ)/1000000 ≤ √5 ∧ √5 ≤ 2236068/1000000 := by
  have hs : (√(5:ℝ))^2=5 := Real.sq_sqrt (by norm_num)
  have hn := Real.sqrt_nonneg (5:ℝ)
  constructor <;> nlinarith

theorem tan_tenth_identity :
    (5+√(5:ℝ))*(tan (π/10))^2 = 3-√5 := by
  have hc : cos (π/10) ≠ 0 := ne_of_gt (cos_pos_of_mem_Ioo (by constructor <;> linarith [pi_pos]))
  have h2 := cos_two_mul (π/10)
  have harg : 2*(π/10)=π/5 := by ring
  rw [harg,cos_pi_div_five] at h2
  have hs := sin_sq_add_cos_sq (π/10)
  rw [tan_eq_sin_div_cos]
  field_simp
  nlinarith

theorem tan_fifth_identity :
    (3+√(5:ℝ))*(tan (π/5))^2 = 5-√5 := by
  have hc : cos (π/5) ≠ 0 := ne_of_gt (cos_pos_of_mem_Ioo (by constructor <;> linarith [pi_pos]))
  have hs := sin_sq_add_cos_sq (π/5)
  have hr : (√(5:ℝ))^2=5 := Real.sq_sqrt (by norm_num)
  have hcos : 8*(cos (π/5))^2=3+√5 := by
    rw [cos_pi_div_five]
    nlinarith
  rw [tan_eq_sin_div_cos]
  field_simp
  nlinarith

theorem tan_tenth_bounds : (3249:ℝ)/10000 ≤ tan (π/10) ∧ tan (π/10) ≤ 3250/10000 := by
  have hp : 0 < tan (π/10) := tan_pos_of_pos_of_lt_pi_div_two (by linarith [pi_pos]) (by linarith [pi_pos])
  have ha : 0 < 5+√(5:ℝ) := by positivity
  have h := tan_tenth_identity
  obtain ⟨hl,hu⟩ := sqrt_five_bounds
  have hlow : ((3249:ℝ)/10000)^2 ≤ (tan (π/10))^2 := by
    apply (mul_le_mul_iff_right₀ ha).mp
    rw [h]
    nlinarith
  have hhigh : (tan (π/10))^2 ≤ ((3250:ℝ)/10000)^2 := by
    apply (mul_le_mul_iff_right₀ ha).mp
    rw [h]
    nlinarith
  constructor <;> nlinarith

theorem tan_fifth_bounds : (7265:ℝ)/10000 ≤ tan (π/5) ∧ tan (π/5) ≤ 7266/10000 := by
  have hp : 0 < tan (π/5) := tan_pos_of_pos_of_lt_pi_div_two (by linarith [pi_pos]) (by linarith [pi_pos])
  have ha : 0 < 3+√(5:ℝ) := by positivity
  have h := tan_fifth_identity
  obtain ⟨hl,hu⟩ := sqrt_five_bounds
  have hlow : ((7265:ℝ)/10000)^2 ≤ (tan (π/5))^2 := by
    apply (mul_le_mul_iff_right₀ ha).mp
    rw [h]
    nlinarith
  have hhigh : (tan (π/5))^2 ≤ ((7266:ℝ)/10000)^2 := by
    apply (mul_le_mul_iff_right₀ ha).mp
    rw [h]
    nlinarith
  constructor <;> nlinarith

theorem tan_three_tenths_bounds :
    (13762:ℝ)/10000 ≤ tan (3*π/10) ∧ tan (3*π/10) ≤ 13765/10000 := by
  have heq : 3*π/10=π/2-π/5 := by ring
  rw [heq,tan_pi_div_two_sub]
  obtain ⟨hl,hu⟩ := tan_fifth_bounds
  have hp : 0 < tan (π/5) := by linarith
  have hid := mul_inv_cancel₀ (ne_of_gt hp)
  have hip : 0 < (tan (π/5))⁻¹ := inv_pos.mpr hp
  constructor
  · nlinarith [mul_nonneg (le_of_lt hip) (sub_nonneg.mpr hu)]
  · nlinarith [mul_nonneg (le_of_lt hip) (sub_nonneg.mpr hl)]

theorem tan_two_fifths_bounds :
    (30769:ℝ)/10000 ≤ tan (2*π/5) ∧ tan (2*π/5) ≤ 30779/10000 := by
  have heq : 2*π/5=π/2-π/10 := by ring
  rw [heq,tan_pi_div_two_sub]
  obtain ⟨hl,hu⟩ := tan_tenth_bounds
  have hp : 0 < tan (π/10) := by linarith
  have hid := mul_inv_cancel₀ (ne_of_gt hp)
  have hip : 0 < (tan (π/10))⁻¹ := inv_pos.mpr hp
  constructor
  · nlinarith [mul_nonneg (le_of_lt hip) (sub_nonneg.mpr hu)]
  · nlinarith [mul_nonneg (le_of_lt hip) (sub_nonneg.mpr hl)]

#print axioms tan_tenth_bounds
#print axioms tan_two_fifths_bounds

end Kobon.TangentBounds
