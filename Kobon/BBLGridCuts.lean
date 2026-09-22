import Kobon.BBLGrid
import Kobon.BBLProfiles

/-! The ordered real reference cuts for the BBL row profiles.
They interleave the old tangent intercepts, the new half-grid intercepts,
and the three central values −ε,0,+ε. -/
namespace Kobon.BBLGridCuts
open Real BBLAnalytic BBLGrid BBLProfiles

noncomputable def leftAngle (r : Nat) (j : Int) : ℝ :=
  ((j:ℝ)-4*(r:ℝ)+1)*alpha r/2
noncomputable def rightAngle (r : Nat) (j : Int) : ℝ :=
  ((j:ℝ)-4*(r:ℝ)-1)*alpha r/2

noncomputable def cut (r : Nat) (ε : ℝ) (j : Int) : ℝ :=
  if j < 4*(r:Int)-1 then tan (leftAngle r j)
  else if j = 4*(r:Int)-1 then -ε
  else if j = 4*(r:Int) then 0
  else if j = 4*(r:Int)+1 then ε
  else tan (rightAngle r j)

theorem left_angle_bounds (r : Nat) (hr : 5 ≤ r) (j : Int)
    (hj : 0 ≤ j) (hj' : j < 4*(r:Int)-1) :
    -π/2 < leftAngle r j ∧ leftAngle r j ≤ -alpha r/2 := by
  obtain ⟨ha,_,hid⟩ := alpha_data r hr
  have hjR : (0:ℝ) ≤ j := by exact_mod_cast hj
  have hjR' : (j:ℝ) ≤ 4*(r:ℝ)-2 := by exact_mod_cast (show j ≤ 4*(r:Int)-2 by omega)
  have hm1 := mul_nonneg hjR (le_of_lt ha)
  have hm2 := mul_le_mul_of_nonneg_right hjR' (le_of_lt ha)
  dsimp [leftAngle]
  constructor <;> nlinarith

theorem right_angle_bounds (r : Nat) (hr : 5 ≤ r) (j : Int)
    (hj : 4*(r:Int)+1 < j) (hj' : j ≤ 8*(r:Int)) :
    alpha r/2 ≤ rightAngle r j ∧ rightAngle r j < π/2 := by
  obtain ⟨ha,_,hid⟩ := alpha_data r hr
  have hjR : 4*(r:ℝ)+2 ≤ (j:ℝ) := by exact_mod_cast (show 4*(r:Int)+2 ≤ j by omega)
  have hjR' : (j:ℝ) ≤ 8*(r:ℝ) := by exact_mod_cast hj'
  have hm1 := mul_le_mul_of_nonneg_right hjR (le_of_lt ha)
  have hm2 := mul_le_mul_of_nonneg_right hjR' (le_of_lt ha)
  dsimp [rightAngle]
  constructor <;> nlinarith

theorem cut_left (r : Nat) (ε : ℝ) (j : Int) (hj : j < 4*(r:Int)-1) :
    cut r ε j = tan (leftAngle r j) := by simp [cut,hj]

theorem cut_right (r : Nat) (ε : ℝ) (j : Int) (hj : 4*(r:Int)+1 < j) :
    cut r ε j = tan (rightAngle r j) := by
  simp [cut,show ¬j < 4*(r:Int)-1 by omega,show j ≠ 4*(r:Int)-1 by omega,
    show j ≠ 4*(r:Int) by omega,show j ≠ 4*(r:Int)+1 by omega]

@[simp] theorem cut_neg (r : Nat) (ε : ℝ) : cut r ε (4*(r:Int)-1) = -ε := by simp [cut]
@[simp] theorem cut_zero (r : Nat) (ε : ℝ) : cut r ε (4*(r:Int)) = 0 := by
  simp [cut,show ¬4*(r:Int) < 4*(r:Int)-1 by omega,show 4*(r:Int) ≠ 4*(r:Int)-1 by omega]
@[simp] theorem cut_pos (r : Nat) (ε : ℝ) : cut r ε (4*(r:Int)+1) = ε := by
  simp [cut,show ¬4*(r:Int)+1 < 4*(r:Int)-1 by omega,
    show 4*(r:Int)+1 ≠ 4*(r:Int)-1 by omega,show 4*(r:Int)+1 ≠ 4*(r:Int) by omega]

theorem cut_left_strict (r : Nat) (hr : 5 ≤ r) (ε : ℝ) (i j : Int)
    (hi : 0 ≤ i) (hj : j < 4*(r:Int)-1) (hij : i < j) : cut r ε i < cut r ε j := by
  have hi' : i < 4*(r:Int)-1 := lt_trans hij hj
  have hj0 : 0 ≤ j := by omega
  obtain ⟨hai,_⟩ := left_angle_bounds r hr i hi hi'
  obtain ⟨_,haj⟩ := left_angle_bounds r hr j hj0 hj
  obtain ⟨ha,_,_⟩ := alpha_data r hr
  rw [cut_left r ε i hi',cut_left r ε j hj]
  apply tan_lt_tan_of_lt_of_lt_pi_div_two (by linarith) (by linarith [pi_pos])
  have hijR : (i:ℝ) < j := by exact_mod_cast hij
  have hm := mul_lt_mul_of_pos_right hijR ha
  dsimp [leftAngle]
  nlinarith

theorem cut_right_strict (r : Nat) (hr : 5 ≤ r) (ε : ℝ) (i j : Int)
    (hi : 4*(r:Int)+1 < i) (hj : j ≤ 8*(r:Int)) (hij : i < j) : cut r ε i < cut r ε j := by
  have hj' : 4*(r:Int)+1 < j := lt_trans hi hij
  have hi' : i ≤ 8*(r:Int) := by omega
  obtain ⟨hai,_⟩ := right_angle_bounds r hr i hi hi'
  obtain ⟨_,haj⟩ := right_angle_bounds r hr j hj' hj
  obtain ⟨ha,_,_⟩ := alpha_data r hr
  rw [cut_right r ε i hi,cut_right r ε j hj']
  apply tan_lt_tan_of_lt_of_lt_pi_div_two (by linarith [pi_pos]) haj
  have hijR : (i:ℝ) < j := by exact_mod_cast hij
  have hm := mul_lt_mul_of_pos_right hijR ha
  dsimp [rightAngle]
  nlinarith

theorem cut_left_below (r : Nat) (hr : 5 ≤ r) (ε : ℝ)
    (hε : ε < tan (alpha r/2)) (j : Int) (hj : 0 ≤ j) (hj' : j < 4*(r:Int)-1) :
    cut r ε j < -ε := by
  obtain ⟨ha,ha2,_⟩ := alpha_data r hr
  obtain ⟨hlo,hhi⟩ := left_angle_bounds r hr j hj hj'
  have ht : tan (leftAngle r j) ≤ tan (-alpha r/2) := by
    apply strictMonoOn_tan.monotoneOn ⟨by linarith,by linarith [pi_pos]⟩
      ⟨by linarith,by linarith [pi_pos]⟩ hhi
  rw [cut_left r ε j hj']
  have heq : -alpha r/2 = -(alpha r/2) := by ring
  rw [heq,tan_neg] at ht
  linarith

theorem cut_right_above (r : Nat) (hr : 5 ≤ r) (ε : ℝ)
    (hε : ε < tan (alpha r/2)) (j : Int)
    (hj : 4*(r:Int)+1 < j) (hj' : j ≤ 8*(r:Int)) : ε < cut r ε j := by
  obtain ⟨ha,ha2,_⟩ := alpha_data r hr
  obtain ⟨hlo,hhi⟩ := right_angle_bounds r hr j hj hj'
  have ht : tan (alpha r/2) ≤ tan (rightAngle r j) := by
    apply strictMonoOn_tan.monotoneOn ⟨by linarith [pi_pos],by linarith⟩
      ⟨by linarith [pi_pos],hhi⟩ hlo
  rw [cut_right r ε j hj]
  linarith

theorem cut_increasing (r : Nat) (hr : 5 ≤ r) (ε : ℝ)
    (hε0 : 0 < ε) (hε : ε < tan (alpha r/2)) :
    IncreasingCuts (8*(r:Int)) (cut r ε) := by
  intro i j hi hj hij
  by_cases hil : i < 4*(r:Int)-1
  · by_cases hjl : j < 4*(r:Int)-1
    · exact cut_left_strict r hr ε i j hi hjl hij
    have hleft := cut_left_below r hr ε hε i hi hil
    by_cases hjr : 4*(r:Int)+1 < j
    · have hright := cut_right_above r hr ε hε j hjr hj
      linarith
    have hcases : j = 4*(r:Int)-1 ∨ j = 4*(r:Int) ∨ j = 4*(r:Int)+1 := by omega
    rcases hcases with h | h | h <;> rw [h] <;> simp only [cut_neg,cut_zero,cut_pos] <;> linarith
  by_cases hir : 4*(r:Int)+1 < i
  · exact cut_right_strict r hr ε i j hir hj hij
  have hicases : i = 4*(r:Int)-1 ∨ i = 4*(r:Int) ∨ i = 4*(r:Int)+1 := by omega
  by_cases hjr : 4*(r:Int)+1 < j
  · have hright := cut_right_above r hr ε hε j hjr hj
    rcases hicases with h | h | h <;> rw [h] <;> simp only [cut_neg,cut_zero,cut_pos] <;> linarith
  have hjcases : j = 4*(r:Int)-1 ∨ j = 4*(r:Int) ∨ j = 4*(r:Int)+1 := by omega
  rcases hicases with h | h | h <;> rcases hjcases with h' | h' | h' <;>
    rw [h,h'] <;> simp only [cut_neg,cut_zero,cut_pos] <;> first | omega | linarith

theorem cut_beta_left (r : Nat) (hr : 5 ≤ r) (ε : ℝ) (i : Fin (4*r))
    (hi : i.val < 2*r) : cut r ε (2*(i.val:Int)) = tan (beta r i) := by
  have hi' : 2*(i.val:Int) < 4*(r:Int)-1 := by omega
  rw [cut_left r ε _ hi']
  congr 1
  obtain ⟨_,_,hid⟩ := alpha_data r hr
  dsimp [leftAngle,beta]
  push_cast
  nlinarith

theorem cut_beta_right (r : Nat) (hr : 5 ≤ r) (ε : ℝ) (i : Fin (4*r))
    (hi : 2*r ≤ i.val) : cut r ε (2*(i.val:Int)+2) = tan (beta r i) := by
  have hi' : 4*(r:Int)+1 < 2*(i.val:Int)+2 := by omega
  rw [cut_right r ε _ hi']
  congr 1
  obtain ⟨_,_,hid⟩ := alpha_data r hr
  dsimp [rightAngle,beta]
  push_cast
  nlinarith

def oldAnchor (r : Nat) (z : Int) : Int :=
  if z < 0 then z+2*(r:Int)-1 else z+2*(r:Int)

theorem anchor_bounds (r : Nat) (z : Int) (hz : -2*(r:Int) < z ∧ z < 2*(r:Int))
    (hz0 : z ≠ 0) : 0 ≤ oldAnchor r z ∧ oldAnchor r z < 4*(r:Int) ∧
      oldAnchor r z ≠ 2*(r:Int)-1 ∧ oldAnchor r z ≠ 2*(r:Int) := by
  unfold oldAnchor
  split_ifs <;> omega

theorem cut_anchor (r : Nat) (ε : ℝ) (z : Int) (hz0 : z ≠ 0) :
    cut r ε (2*oldAnchor r z+1) = tan ((z:ℝ)*alpha r) := by
  unfold oldAnchor
  split_ifs with hz
  · have hj : 2*(z+2*(r:Int)-1)+1 < 4*(r:Int)-1 := by omega
    rw [cut_left r ε _ hj]
    congr 1
    dsimp [leftAngle]
    push_cast
    ring
  · have hj : 4*(r:Int)+1 < 2*(z+2*(r:Int))+1 := by omega
    rw [cut_right r ε _ hj]
    congr 1
    dsimp [rightAngle]
    push_cast
    ring

theorem rational_sum_anchor (r : Nat) (hr : 5 ≤ r) (ε : ℝ)
    (i k : Fin (4*r)) (hik : i ≠ k)
    (hl : sumIndex r i k ≠ -2*(r:Int)) (hu : sumIndex r i k ≠ 2*(r:Int))
    (hz : reducedIndex r (sumIndex r i k) ≠ 0) :
    (tan (beta r i)+tan (beta r k))/(1-tan (beta r i)*tan (beta r k)) =
      cut r ε (2*oldAnchor r (reducedIndex r (sumIndex r i k))+1) := by
  rw [tangent_sum_rational _ _ (ne_of_gt (beta_cos_pos r hr i))
    (ne_of_gt (beta_cos_pos r hr k)) (sum_cos_ne_zero r hr i k hik hl hu),
    sum_tangent r hr i k,cut_anchor r ε _ hz]

#print axioms cut_increasing
#print axioms rational_sum_anchor
end Kobon.BBLGridCuts
