import Kobon.TangentBounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

/-! Sharp rational enclosures for the actual nine positive tangent-grid values.
All inequalities are checked from trigonometric identities in Lean.
-/
namespace Kobon.BBLTangentBounds
open Real
set_option maxHeartbeats 0

theorem inverse_bounds (x L U : ℝ) (hx : 0<x) (hL : 0≤L) (hU : 0≤U)
    (hl : L*x≤1) (hu : 1≤U*x) : L≤x⁻¹ ∧ x⁻¹≤U := by
  have hi := mul_inv_cancel₀ (ne_of_gt hx)
  constructor
  · by_contra h
    have hmul := mul_pos (sub_pos.mpr (lt_of_not_ge h)) hx
    nlinarith
  · by_contra h
    have hmul := mul_pos (sub_pos.mpr (lt_of_not_ge h)) hx
    nlinarith

theorem half_bounds (t A L U Alo Ahi : ℝ) (ht : 0<t) (ht1 : t<1)
    (hA : 0<A) (hAl : Alo≤A) (hAu : A≤Ahi)
    (hL : 0≤L) (hL1 : L<1) (hU : 0≤U) (hU1 : U<1)
    (hid : A*(1-t^2)=2*t)
    (hl : 2*L≤Alo*(1-L^2)) (hu : Ahi*(1-U^2)≤2*U) : L≤t ∧ t≤U := by
  have hls : 0≤1-L^2 := by nlinarith
  have hus : 0≤1-U^2 := by nlinarith
  have hlow : 2*L≤A*(1-L^2) := le_trans hl (mul_le_mul_of_nonneg_right hAl hls)
  have hupp : A*(1-U^2)≤2*U := le_trans (mul_le_mul_of_nonneg_right hAu hus) hu
  constructor
  · by_contra h
    have htl : t<L := lt_of_not_ge h
    have hs : 0<L^2-t^2 := by nlinarith
    have hm := mul_pos hA hs
    nlinarith
  · by_contra h
    have hut : U<t := lt_of_not_ge h
    have hs : 0<t^2-U^2 := by nlinarith
    have hm := mul_pos hA hs
    nlinarith

theorem tan_small (x : ℝ) (hx : 0<x) (hx4 : x<π/4) :
    0<tan x ∧ tan x<1 := by
  constructor
  · exact tan_pos_of_pos_of_lt_pi_div_two hx (by linarith [pi_pos])
  · rw [← tan_pi_div_four]
    apply strictMonoOn_tan
    · constructor <;> linarith [pi_pos]
    · constructor <;> linarith [pi_pos]
    · exact hx4

theorem tan_half_identity (x : ℝ) (hx : 0<x) (hx4 : x<π/4) :
    tan (2*x)*(1-(tan x)^2)=2*tan x := by
  obtain ⟨hp,hu⟩ := tan_small x hx hx4
  have hn : 1-(tan x)^2 ≠ 0 := by nlinarith
  rw [tan_two_mul]
  exact div_mul_cancel₀ _ hn

theorem sqrt_five_sharp : (223606797749978969640917366873127623544061835961152:ℝ)/100000000000000000000000000000000000000000000000000 ≤ √5 ∧ √5 ≤ 223606797749978969640917366873127623544061835961153/100000000000000000000000000000000000000000000000000 := by
  have hs : (√(5:ℝ))^2=5 := Real.sq_sqrt (by norm_num)
  have hn := Real.sqrt_nonneg (5:ℝ)
  constructor <;> nlinarith

theorem tan_2_bounds : (3249196962329063261558714122151344649549:ℝ)/10000000000000000000000000000000000000000 ≤ tan (2*π/20) ∧ tan (2*π/20) ≤ (3249196962329063261558714122151344649550:ℝ)/10000000000000000000000000000000000000000 := by
  have heq : 2*π/20=π/10 := by ring
  rw [heq]
  have hp : 0 < tan (π/10) := tan_pos_of_pos_of_lt_pi_div_two (by linarith [pi_pos]) (by linarith [pi_pos])
  have ha : 0 < 5+√(5:ℝ) := by positivity
  have h := TangentBounds.tan_tenth_identity
  obtain ⟨hl,hu⟩ := sqrt_five_sharp
  have hlow : ((3249196962329063261558714122151344649549:ℝ)/10000000000000000000000000000000000000000)^2 ≤ (tan (π/10))^2 := by
    apply (mul_le_mul_iff_right₀ ha).mp
    rw [h]
    nlinarith
  have hhigh : (tan (π/10))^2 ≤ ((3249196962329063261558714122151344649550:ℝ)/10000000000000000000000000000000000000000)^2 := by
    apply (mul_le_mul_iff_right₀ ha).mp
    rw [h]
    nlinarith
  constructor <;> nlinarith

theorem tan_4_bounds : (7265425280053608858954667574806187496160:ℝ)/10000000000000000000000000000000000000000 ≤ tan (4*π/20) ∧ tan (4*π/20) ≤ (7265425280053608858954667574806187496161:ℝ)/10000000000000000000000000000000000000000 := by
  have heq : 4*π/20=π/5 := by ring
  rw [heq]
  have hp : 0 < tan (π/5) := tan_pos_of_pos_of_lt_pi_div_two (by linarith [pi_pos]) (by linarith [pi_pos])
  have ha : 0 < 3+√(5:ℝ) := by positivity
  have h := TangentBounds.tan_fifth_identity
  obtain ⟨hl,hu⟩ := sqrt_five_sharp
  have hlow : ((7265425280053608858954667574806187496160:ℝ)/10000000000000000000000000000000000000000)^2 ≤ (tan (π/5))^2 := by
    apply (mul_le_mul_iff_right₀ ha).mp
    rw [h]
    nlinarith
  have hhigh : (tan (π/5))^2 ≤ ((7265425280053608858954667574806187496161:ℝ)/10000000000000000000000000000000000000000)^2 := by
    apply (mul_le_mul_iff_right₀ ha).mp
    rw [h]
    nlinarith
  constructor <;> nlinarith

theorem tan_6_bounds : (137638192047117353820720958191088767:ℝ)/100000000000000000000000000000000000 ≤ tan (6*π/20) ∧ tan (6*π/20) ≤ (137638192047117353820720958191088768:ℝ)/100000000000000000000000000000000000 := by
  have heq : 6*π/20=π/2-4*π/20 := by ring
  rw [heq,tan_pi_div_two_sub]
  obtain ⟨hl,hu⟩ := tan_4_bounds
  have hp : 0<tan (4*π/20) := by linarith
  apply inverse_bounds _ _ _ hp (by norm_num) (by norm_num)
  · nlinarith
  · nlinarith

theorem tan_8_bounds : (307768353717525340257029057603690982:ℝ)/100000000000000000000000000000000000 ≤ tan (8*π/20) ∧ tan (8*π/20) ≤ (307768353717525340257029057603690983:ℝ)/100000000000000000000000000000000000 := by
  have heq : 8*π/20=π/2-2*π/20 := by ring
  rw [heq,tan_pi_div_two_sub]
  obtain ⟨hl,hu⟩ := tan_2_bounds
  have hp : 0<tan (2*π/20) := by linarith
  apply inverse_bounds _ _ _ hp (by norm_num) (by norm_num)
  · nlinarith
  · nlinarith

theorem tan_1_bounds : (158384440324536293838883092694:ℝ)/1000000000000000000000000000000 ≤ tan (1*π/20) ∧ tan (1*π/20) ≤ (158384440324536293838883092695:ℝ)/1000000000000000000000000000000 := by
  obtain ⟨hp,hu⟩ := tan_small (1*π/20) (by linarith [pi_pos]) (by linarith [pi_pos])
  have hid := tan_half_identity (1*π/20) (by linarith [pi_pos]) (by linarith [pi_pos])
  have heq : 2*(1*π/20)=2*π/20 := by ring
  rw [heq] at hid
  obtain ⟨hAl,hAu⟩ := tan_2_bounds
  exact half_bounds _ _ _ _ ((3249196962329063261558714122151344649549:ℝ)/10000000000000000000000000000000000000000) ((3249196962329063261558714122151344649550:ℝ)/10000000000000000000000000000000000000000) hp hu
    (by linarith) hAl hAu (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hid (by norm_num) (by norm_num)

theorem tan_3_bounds : (509525449494428810513706911250:ℝ)/1000000000000000000000000000000 ≤ tan (3*π/20) ∧ tan (3*π/20) ≤ (509525449494428810513706911251:ℝ)/1000000000000000000000000000000 := by
  obtain ⟨hp,hu⟩ := tan_small (3*π/20) (by linarith [pi_pos]) (by linarith [pi_pos])
  have hid := tan_half_identity (3*π/20) (by linarith [pi_pos]) (by linarith [pi_pos])
  have heq : 2*(3*π/20)=6*π/20 := by ring
  rw [heq] at hid
  obtain ⟨hAl,hAu⟩ := tan_6_bounds
  exact half_bounds _ _ _ _ ((137638192047117353820720958191088767:ℝ)/100000000000000000000000000000000000) ((137638192047117353820720958191088768:ℝ)/100000000000000000000000000000000000) hp hu
    (by linarith) hAl hAu (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hid (by norm_num) (by norm_num)

theorem tan_5_bounds : (1000000000000000000000000000000:ℝ)/1000000000000000000000000000000 ≤ tan (5*π/20) ∧ tan (5*π/20) ≤ (1000000000000000000000000000000:ℝ)/1000000000000000000000000000000 := by
  have heq : 5*π/20=π/4 := by ring
  rw [heq,tan_pi_div_four]
  norm_num

theorem tan_7_bounds : (19626105055051505823046404:ℝ)/10000000000000000000000000 ≤ tan (7*π/20) ∧ tan (7*π/20) ≤ (19626105055051505823046405:ℝ)/10000000000000000000000000 := by
  have heq : 7*π/20=π/2-3*π/20 := by ring
  rw [heq,tan_pi_div_two_sub]
  obtain ⟨hl,hu⟩ := tan_3_bounds
  have hp : 0<tan (3*π/20) := by linarith
  apply inverse_bounds _ _ _ hp (by norm_num) (by norm_num)
  · nlinarith
  · nlinarith

theorem tan_9_bounds : (63137515146750430989794642:ℝ)/10000000000000000000000000 ≤ tan (9*π/20) ∧ tan (9*π/20) ≤ (63137515146750430989794643:ℝ)/10000000000000000000000000 := by
  have heq : 9*π/20=π/2-1*π/20 := by ring
  rw [heq,tan_pi_div_two_sub]
  obtain ⟨hl,hu⟩ := tan_1_bounds
  have hp : 0<tan (1*π/20) := by linarith
  apply inverse_bounds _ _ _ hp (by norm_num) (by norm_num)
  · nlinarith
  · nlinarith

#print axioms tan_1_bounds
#print axioms tan_9_bounds
end Kobon.BBLTangentBounds
