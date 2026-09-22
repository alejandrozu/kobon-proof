import Kobon.BBLMaximization
import Kobon.BBLExtrema
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! Uniform analytic estimates for the BBL line pencil. -/
namespace Kobon.BBLAnalytic
open Real BBLExtrema BBLMaximization
set_option maxHeartbeats 0

theorem abs_self_le_abs_tan (x : ℝ) (hx : |x| < π/2) : |x| ≤ |tan x| := by
  by_cases hp : 0 ≤ x
  · have htan : 0 ≤ tan x := tan_nonneg_of_nonneg_of_le_pi_div_two hp (by
      rw [abs_of_nonneg hp] at hx
      exact le_of_lt hx)
    rw [abs_of_nonneg hp,abs_of_nonneg htan]
    exact le_tan hp (by simpa [abs_of_nonneg hp] using hx)
  · have hn : x < 0 := lt_of_not_ge hp
    have htan : tan x < 0 := tan_neg_of_neg_of_pi_div_two_lt hn (by
      rw [abs_of_neg hn] at hx
      linarith)
    have hh := le_tan (x := -x) (by linarith) (by simpa [abs_of_neg hn] using hx)
    simpa [abs_of_neg hn,abs_of_neg htan,tan_neg] using hh

theorem cotangent_bound (q x : ℝ) (hq : 20 ≤ q)
    (hx : |x| < π/2) (haway : π/(2*q) ≤ |x|) : |1/tan x| ≤ q := by
  have hqpos : 0 < q := by linarith
  have htan := abs_self_le_abs_tan x hx
  have hmin : 1/q  ≤  π/(2*q) := by
    apply (div_le_div_iff₀ hqpos (by positivity)).mpr
    nlinarith [two_le_pi]
  have htp : 0 < |tan x| := lt_of_lt_of_le (div_pos (by norm_num) hqpos)
    (le_trans hmin (le_trans haway htan))
  rw [abs_div,abs_one]
  apply (div_le_iff₀ htp).mpr
  have hh : 1/q ≤ |tan x| := le_trans hmin (le_trans haway htan)
  have hm := mul_le_mul_of_nonneg_left hh (le_of_lt hqpos)
  have hid : q*(1/q)=1 := by field_simp
  rw [hid] at hm
  exact hm

noncomputable def alpha (r : Nat) : ℝ := π/(4*(r:ℝ))
noncomputable def beta (r : Nat) (i : Fin (4*r)) : ℝ :=
  -π/2+((i.val:ℝ)+1/2)*alpha r

theorem alpha_data (r : Nat) (hr : 5 ≤ r) :
    0 < alpha r ∧ alpha r < π/2 ∧ (4*(r:ℝ))*alpha r=π := by
  have hR : (5:ℝ) ≤ r := by exact_mod_cast hr
  have hp : 0 < (r:ℝ) := by linarith
  have ha : 0 < alpha r := div_pos pi_pos (by positivity)
  have hid : (4*(r:ℝ))*alpha r=π := by dsimp [alpha]; field_simp
  exact ⟨ha,by nlinarith,hid⟩

theorem beta_data (r : Nat) (hr : 5 ≤ r) (i : Fin (4*r)) :
    -π/2+alpha r/2 ≤ beta r i ∧ beta r i ≤ π/2-alpha r/2 ∧
      (alpha r/2 ≤ beta r i ∨ beta r i ≤ -(alpha r/2)) := by
  obtain ⟨ha,ha2,hid⟩ := alpha_data r hr
  have hi0 : (0:ℝ) ≤ i.val := by positivity
  have hi1 : (i.val:ℝ)+1 ≤ 4*(r:ℝ) := by exact_mod_cast i.isLt
  have hlow : -π/2+alpha r/2 ≤ beta r i := by
    dsimp [beta]
    nlinarith [mul_nonneg hi0 (le_of_lt ha)]
  have hhigh : beta r i ≤ π/2-alpha r/2 := by
    have hm := mul_le_mul_of_nonneg_right hi1 (le_of_lt ha)
    dsimp [beta]
    nlinarith
  refine ⟨hlow,hhigh,?_⟩
  by_cases hi : i.val < 2*r
  · right
    have hic : (i.val:ℝ)+1 ≤ 2*(r:ℝ) := by exact_mod_cast hi
    have hm := mul_le_mul_of_nonneg_right hic (le_of_lt ha)
    dsimp [beta]
    nlinarith
  · left
    have hic : 2*(r:ℝ) ≤ i.val := by exact_mod_cast (show 2*r ≤ i.val by omega)
    have hm := mul_le_mul_of_nonneg_right hic (le_of_lt ha)
    dsimp [beta]
    nlinarith

theorem beta_cot_bound (r : Nat) (hr : 5 ≤ r) (i : Fin (4*r)) :
    |1/tan (beta r i)| ≤ 4*(r:ℝ) := by
  obtain ⟨ha,ha2,hid⟩ := alpha_data r hr
  obtain ⟨hblo,hbhi,hgap⟩ := beta_data r hr i
  have hq : (20:ℝ) ≤ 4*(r:ℝ) := by exact_mod_cast (show 20 ≤ 4*r by omega)
  apply cotangent_bound _ _ hq
  · rw [abs_lt]
    constructor  <;>  linarith
  · have heq : π/(2*(4*(r:ℝ)))=alpha r/2 := by dsimp [alpha]; ring
    rw [heq]
    rcases hgap with h | h
    · exact le_trans h (le_abs_self _)
    · exact le_trans (by linarith) (neg_le_abs _)

theorem beta_tan_bound (r : Nat) (hr : 5 ≤ r) (i : Fin (4*r)) :
    |tan (beta r i)| ≤ 4*(r:ℝ) := by
  obtain ⟨ha,ha2,hid⟩ := alpha_data r hr
  obtain ⟨hblo,hbhi,hgap⟩ := beta_data r hr i
  have hbabs : |beta r i| ≤ π/2-alpha r/2 := abs_le.mpr ⟨by linarith,hbhi⟩
  have habsp : 0 < |beta r i| := by
    rcases hgap with h | h
    · exact lt_of_lt_of_le (by linarith : 0 < alpha r/2) (le_trans h (le_abs_self _))
    · exact lt_of_lt_of_le (by linarith : 0 < alpha r/2) (le_trans (by linarith) (neg_le_abs _))
  have hq : (20:ℝ) ≤ 4*(r:ℝ) := by exact_mod_cast (show 20 ≤ 4*r by omega)
  have hxpos : 0 < π/2-|beta r i| := by linarith
  have hcot := cotangent_bound (4*(r:ℝ)) (π/2-|beta r i|) hq
    (by rw [abs_of_pos hxpos]; linarith)
    (by rw [abs_of_pos hxpos]; dsimp [alpha] at hbabs; convert sub_le_sub_left hbabs (π/2) using 1  <;>  ring)
  rw [tan_pi_div_two_sub,one_div,inv_inv] at hcot
  by_cases hp : 0 ≤ beta r i
  · simpa [abs_of_nonneg hp] using hcot
  · have hn : beta r i < 0 := lt_of_not_ge hp
    simpa [abs_of_neg hn,tan_neg] using hcot

#print axioms beta_cot_bound
#print axioms beta_tan_bound
end Kobon.BBLAnalytic
