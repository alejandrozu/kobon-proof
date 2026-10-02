import Kobon.BBLTangentAlgebra
import Mathlib.Tactic.IntervalCases

/-! Exact power-basis expressions for every noncentral intercept in the
20-line tangent grid. Every polynomial identity is kernel checked. -/
namespace Kobon.BBLTangentValues
open Real BBLTangentAlgebra BBLGrid
set_option maxHeartbeats 0

noncomputable def value : Nat → ℝ → ℝ
  | 0, t => 0
  | 1, t => t
  | 2, t => -3*t^3/10 + 7*t^2/5 + 31*t/10 - 1/5
  | 3, t => -t^3 + 9*t^2/2 + 12*t - 3/2
  | 4, t => t^3/2 - 5*t^2/2 - 9*t/2 + 3/2
  | 5, t => 1
  | 6, t => -t^3/10 + 3*t^2/10 + 17*t/10 + 11/10
  | 7, t => -t^2/2 + 3*t + 3/2
  | 8, t => -t^3/2 + 2*t^2 + 13*t/2 + 2
  | 9, t => -t^3 + 4*t^2 + 14*t + 4
  | _, _ => 0

theorem value_step (t : ℝ) (hq : quartic t=0) (k : Nat) (hk : k<9) :
    value (k+1) t*(1-value k t*t)=value k t+t := by
  interval_cases k
  · norm_num only [value]
    unfold quartic at hq
    linear_combination (0)*hq
  · norm_num only [value]
    unfold quartic at hq
    linear_combination (3*t/10 - 1/5)*hq
  · norm_num only [value]
    unfold quartic at hq
    linear_combination (-3*t^3/10 + 31*t^2/20 + 12*t/5 - 13/10)*hq
  · norm_num only [value]
    unfold quartic at hq
    linear_combination (t^3/2 - 11*t^2/4 - 13*t/4 + 3)*hq
  · norm_num only [value]
    unfold quartic at hq
    linear_combination (-1/2)*hq
  · norm_num only [value]
    unfold quartic at hq
    linear_combination (1/10)*hq
  · norm_num only [value]
    unfold quartic at hq
    linear_combination (-t^2/20 + t/4 + 2/5)*hq
  · norm_num only [value]
    unfold quartic at hq
    linear_combination (-t^2/4 + 3*t/2 + 1/2)*hq
  · norm_num only [value]
    unfold quartic at hq
    linear_combination (-t^3/2 + 2*t^2 + 13*t/2 + 2)*hq

theorem multiple_cos_pos (k : Nat) (hk : k<10) :
    0<cos ((k:ℝ)*(π/20)) := by
  have hkn : (0:ℝ)≤k := Nat.cast_nonneg k
  have hku : (k:ℝ)<10 := by exact_mod_cast hk
  apply cos_pos_of_mem_Ioo
  constructor <;> nlinarith [pi_pos,mul_nonneg hkn (le_of_lt pi_pos),
    mul_pos (sub_pos.mpr hku) pi_pos]

theorem value_eq_tan (k : Nat) (hk : k<10) :
    value k (tan (π/20))=tan ((k:ℝ)*(π/20)) := by
  induction k with
  | zero => simp [value]
  | succ k ih =>
    have hk9 : k<9 := by omega
    have ih := ih (by omega)
    have hc0 : cos (π/20)≠0 := ne_of_gt (by simpa using multiple_cos_pos 1 (by norm_num))
    have hck : cos ((k:ℝ)*(π/20))≠0 := ne_of_gt (multiple_cos_pos k (by omega))
    have hcs : cos ((k:ℝ)*(π/20)+π/20)≠0 := by
      have he : (k:ℝ)*(π/20)+π/20=((k+1:Nat):ℝ)*(π/20) := by push_cast; ring
      rw [he]
      exact ne_of_gt (multiple_cos_pos (k+1) hk)
    have hd : 1-tan ((k:ℝ)*(π/20))*tan (π/20)≠0 := by
      intro hh
      have hp := tangent_product_identity ((k:ℝ)*(π/20)) (π/20) hck hc0
      rw [hh,zero_mul] at hp
      exact hcs hp.symm
    have hs := value_step (tan (π/20)) tan_quartic k hk9
    rw [ih] at hs
    have hh := tangent_sum_rational ((k:ℝ)*(π/20)) (π/20) hck hc0 hcs
    have he : ((k+1:Nat):ℝ)*(π/20)=(k:ℝ)*(π/20)+π/20 := by push_cast; ring
    rw [he,←hh]
    exact (eq_div_iff hd).mpr hs

#print axioms value_eq_tan
end Kobon.BBLTangentValues
