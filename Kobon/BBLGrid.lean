import Kobon.BBLAnalytic
import Kobon.BBLIntersection

/-! Trigonometric identities and ordering for the BBL tangent grid. -/
namespace Kobon.BBLGrid
open Real BBLAnalytic BBLIntersection
set_option maxRecDepth 10000

def sumIndex (r : Nat) (i k : Fin (4*r)) : Int :=
  (i.val:Int)+(k.val:Int)-4*(r:Int)+1

def reducedIndex (r : Nat) (s : Int) : Int :=
  if s < -2*(r:Int) then s+4*(r:Int)
  else if 2*(r:Int) < s then s-4*(r:Int) else s

theorem beta_cos_pos (r : Nat) (hr : 5 ≤ r) (i : Fin (4*r)) :
    0 < cos (beta r i) := by
  obtain ⟨ha,_,_⟩ := alpha_data r hr
  obtain ⟨hl,hu,_⟩ := beta_data r hr i
  exact cos_pos_of_mem_Ioo ⟨by linarith,by linarith⟩

theorem beta_tan_ne_zero (r : Nat) (hr : 5 ≤ r) (i : Fin (4*r)) :
    tan (beta r i) ≠ 0 := by
  obtain ⟨ha,_,_⟩ := alpha_data r hr
  obtain ⟨hl,hu,hgap⟩ := beta_data r hr i
  rcases hgap with hp | hn
  · exact ne_of_gt (tan_pos_of_pos_of_lt_pi_div_two (by linarith) (by linarith))
  · exact ne_of_lt (tan_neg_of_neg_of_pi_div_two_lt (by linarith) (by linarith))

theorem beta_tan_strictMono (r : Nat) (hr : 5 ≤ r) :
    StrictMono (fun i : Fin (4*r) => tan (beta r i)) := by
  intro i k hik
  obtain ⟨ha,_,_⟩ := alpha_data r hr
  obtain ⟨hli,hui,_⟩ := beta_data r hr i
  obtain ⟨hlk,huk,_⟩ := beta_data r hr k
  have hcast : (i.val:ℝ) < k.val := by exact_mod_cast hik
  apply tan_lt_tan_of_lt_of_lt_pi_div_two (by linarith) (by linarith)
  dsimp [beta]
  nlinarith

theorem sum_angle (r : Nat) (hr : 5 ≤ r) (i k : Fin (4*r)) :
    beta r i+beta r k = (sumIndex r i k:ℝ)*alpha r := by
  obtain ⟨_,_,hid⟩ := alpha_data r hr
  dsimp [beta,sumIndex]
  push_cast
  nlinarith

theorem sum_index_bounds (r : Nat) (i k : Fin (4*r)) (hik : i ≠ k) :
    -4*(r:Int)+2 ≤ sumIndex r i k ∧ sumIndex r i k ≤ 4*(r:Int)-2 := by
  have hi := i.isLt
  have hk := k.isLt
  have hine : i.val ≠ k.val := by intro hh; exact hik (Fin.ext hh)
  unfold sumIndex
  omega

theorem reduced_bounds (r : Nat) (s : Int)
    (hs : -4*(r:Int) < s ∧ s < 4*(r:Int))
    (hl : s ≠ -2*(r:Int)) (hu : s ≠ 2*(r:Int)) :
    -2*(r:Int) < reducedIndex r s ∧ reducedIndex r s < 2*(r:Int) := by
  unfold reducedIndex
  split_ifs <;> omega

theorem reduced_angle_bounds (r : Nat) (hr : 5 ≤ r) (s : Int)
    (hs : -4*(r:Int) < s ∧ s < 4*(r:Int))
    (hl : s ≠ -2*(r:Int)) (hu : s ≠ 2*(r:Int)) :
    -π/2 < (reducedIndex r s:ℝ)*alpha r ∧
      (reducedIndex r s:ℝ)*alpha r < π/2 := by
  obtain ⟨ha,_,hid⟩ := alpha_data r hr
  obtain ⟨hlow,hhigh⟩ := reduced_bounds r s hs hl hu
  have hlow' : -2*(r:ℝ) < (reducedIndex r s:ℝ) := by exact_mod_cast hlow
  have hhigh' : (reducedIndex r s:ℝ) < 2*(r:ℝ) := by exact_mod_cast hhigh
  have h1 := mul_lt_mul_of_pos_right hlow' ha
  have h2 := mul_lt_mul_of_pos_right hhigh' ha
  constructor <;> nlinarith

theorem reduced_tangent (r : Nat) (hr : 5 ≤ r) (s : Int) :
    tan ((s:ℝ)*alpha r) = tan ((reducedIndex r s:ℝ)*alpha r) := by
  obtain ⟨_,_,hid⟩ := alpha_data r hr
  unfold reducedIndex
  split_ifs with hl hu
  · have heq : ((s+4*(r:Int):Int):ℝ)*alpha r = (s:ℝ)*alpha r+π := by
      push_cast
      nlinarith
    rw [heq,tan_add_pi]
  · have heq : ((s-4*(r:Int):Int):ℝ)*alpha r = (s:ℝ)*alpha r-π := by
      push_cast
      nlinarith
    rw [heq,tan_sub_pi]
  · rfl

theorem sum_tangent (r : Nat) (hr : 5 ≤ r) (i k : Fin (4*r)) :
    tan (beta r i+beta r k) = tan ((reducedIndex r (sumIndex r i k):ℝ)*alpha r) := by
  rw [sum_angle r hr i k]
  exact reduced_tangent r hr _

/-- The rational slope factor is exactly the trigonometric BBL slope factor. -/
theorem factor_trigonometric (b δ : ℝ) (hb : cos b ≠ 0) :
    slopeFactor δ (tan b) = sin (2*b)+δ/tan b := by
  have h1 : 2*tan b/(1+(tan b)^2) = sin (2*b) := by
    rw [tan_eq_sin_div_cos,sin_two_mul]
    field_simp
    have hid := congrArg (fun z : ℝ => sin b*z) (sin_sq_add_cos_sq b)
    nlinarith only [hid]
  exact congrArg (fun x => x+δ/tan b) h1

/-- An elementary addition identity with denominators explicitly checked. -/
theorem tangent_sum_rational (b c : ℝ) (hb : cos b ≠ 0) (hc : cos c ≠ 0)
    (hbc : cos (b+c) ≠ 0) :
    (tan b+tan c)/(1-tan b*tan c) = tan (b+c) := by
  rw [tan_eq_sin_div_cos,tan_eq_sin_div_cos,tan_eq_sin_div_cos,
    sin_add,cos_add] at *
  field_simp
  <;> ring

theorem tangent_product_identity (b c : ℝ) (hb : cos b ≠ 0) (hc : cos c ≠ 0) :
    (1-tan b*tan c)*(cos b*cos c) = cos (b+c) := by
  rw [tan_eq_sin_div_cos,tan_eq_sin_div_cos,cos_add]
  field_simp
  <;> ring

theorem tangent_product_complementary (r : Nat) (hr : 5 ≤ r) (i k : Fin (4*r))
    (hs : sumIndex r i k = -2*(r:Int) ∨ sumIndex r i k = 2*(r:Int)) :
    tan (beta r i)*tan (beta r k) = 1 := by
  obtain ⟨_,_,hid⟩ := alpha_data r hr
  have hprod := tangent_product_identity (beta r i) (beta r k)
    (ne_of_gt (beta_cos_pos r hr i)) (ne_of_gt (beta_cos_pos r hr k))
  have hsum := sum_angle r hr i k
  have hcos : cos (beta r i+beta r k) = 0 := by
    rcases hs with hs | hs
    · rw [hs] at hsum
      push_cast at hsum
      have heq : beta r i+beta r k = -(π/2) := by nlinarith
      rw [heq,cos_neg,cos_pi_div_two]
    · rw [hs] at hsum
      push_cast at hsum
      have heq : beta r i+beta r k = π/2 := by nlinarith
      rw [heq,cos_pi_div_two]
  rw [hcos] at hprod
  have hn : cos (beta r i)*cos (beta r k) ≠ 0 :=
    mul_ne_zero (ne_of_gt (beta_cos_pos r hr i)) (ne_of_gt (beta_cos_pos r hr k))
  have hz := (mul_eq_zero.mp hprod).resolve_right hn
  linarith

theorem sum_cos_ne_zero (r : Nat) (hr : 5 ≤ r) (i k : Fin (4*r)) (hik : i ≠ k)
    (hl : sumIndex r i k ≠ -2*(r:Int)) (hu : sumIndex r i k ≠ 2*(r:Int)) :
    cos (beta r i+beta r k) ≠ 0 := by
  obtain ⟨ha,_,hid⟩ := alpha_data r hr
  have hsb := sum_index_bounds r i k hik
  have hsb' : -4*(r:Int) < sumIndex r i k ∧ sumIndex r i k < 4*(r:Int) := by omega
  obtain ⟨hlo,hhi⟩ := reduced_angle_bounds r hr _ hsb' hl hu
  have hc := ne_of_gt (cos_pos_of_mem_Ioo ⟨(by linarith : -(π/2) <
    (reducedIndex r (sumIndex r i k):ℝ)*alpha r),hhi⟩)
  rw [sum_angle r hr i k]
  unfold reducedIndex at hc
  split_ifs at hc with hlow hhigh
  · have heq : ((sumIndex r i k+4*(r:Int):Int):ℝ)*alpha r =
        (sumIndex r i k:ℝ)*alpha r+π := by push_cast; nlinarith
    rw [heq,cos_add_pi] at hc
    exact neg_ne_zero.mp hc
  · have heq : ((sumIndex r i k-4*(r:Int):Int):ℝ)*alpha r =
        (sumIndex r i k:ℝ)*alpha r-π := by push_cast; nlinarith
    rw [heq,cos_sub_pi] at hc
    exact neg_ne_zero.mp hc
  · exact hc

theorem tangent_product_noncomplementary (r : Nat) (hr : 5 ≤ r) (i k : Fin (4*r))
    (hik : i ≠ k) (hl : sumIndex r i k ≠ -2*(r:Int))
    (hu : sumIndex r i k ≠ 2*(r:Int)) :
    1-tan (beta r i)*tan (beta r k) ≠ 0 := by
  have hid := tangent_product_identity (beta r i) (beta r k)
    (ne_of_gt (beta_cos_pos r hr i)) (ne_of_gt (beta_cos_pos r hr k))
  intro hz
  rw [hz,zero_mul] at hid
  exact sum_cos_ne_zero r hr i k hik hl hu hid.symm

theorem tangent_pair_sum_neg (b c : ℝ)
    (hb : -π/2 < b ∧ b < π/2) (hc : -π/2 < c ∧ c < π/2)
    (hs : b+c < 0) : tan b+tan c < 0 := by
  have ht := tan_lt_tan_of_lt_of_lt_pi_div_two (show -(π/2) < b by linarith) (show -c < π/2 by linarith)
    (show b < -c by linarith)
  rw [tan_neg] at ht
  linarith

theorem tangent_pair_sum_pos (b c : ℝ)
    (hb : -π/2 < b ∧ b < π/2) (hc : -π/2 < c ∧ c < π/2)
    (hs : 0 < b+c) : 0 < tan b+tan c := by
  have ht := tan_lt_tan_of_lt_of_lt_pi_div_two (show -(π/2) < -c by linarith) hb.2
    (show -c < b by linarith)
  rw [tan_neg] at ht
  linarith

theorem beta_tan_negative (r : Nat) (hr : 5 ≤ r) (i : Fin (4*r))
    (hi : i.val < 2*r) : tan (beta r i) < 0 := by
  obtain ⟨ha,_,hid⟩ := alpha_data r hr
  obtain ⟨hlo,_,_⟩ := beta_data r hr i
  have hiR : (i.val:ℝ)+1 ≤ 2*(r:ℝ) := by exact_mod_cast hi
  have hm := mul_le_mul_of_nonneg_right hiR (le_of_lt ha)
  have hb : beta r i < 0 := by dsimp [beta]; nlinarith
  exact tan_neg_of_neg_of_pi_div_two_lt hb (by linarith)

theorem beta_tan_positive (r : Nat) (hr : 5 ≤ r) (i : Fin (4*r))
    (hi : 2*r ≤ i.val) : 0 < tan (beta r i) := by
  obtain ⟨ha,_,hid⟩ := alpha_data r hr
  obtain ⟨_,hhi,_⟩ := beta_data r hr i
  have hiR : 2*(r:ℝ) ≤ i.val := by exact_mod_cast hi
  have hm := mul_le_mul_of_nonneg_right hiR (le_of_lt ha)
  have hb : 0 < beta r i := by dsimp [beta]; nlinarith
  exact tan_pos_of_pos_of_lt_pi_div_two hb (by linarith)

theorem sum_tan_negative (r : Nat) (hr : 5 ≤ r) (i k : Fin (4*r))
    (hs : sumIndex r i k < 0) : tan (beta r i)+tan (beta r k) < 0 := by
  obtain ⟨ha,_,_⟩ := alpha_data r hr
  obtain ⟨hil,hih,_⟩ := beta_data r hr i
  obtain ⟨hkl,hkh,_⟩ := beta_data r hr k
  apply tangent_pair_sum_neg _ _ ⟨by linarith,by linarith⟩ ⟨by linarith,by linarith⟩
  rw [sum_angle r hr i k]
  exact mul_neg_of_neg_of_pos (by exact_mod_cast hs) ha

theorem sum_tan_positive (r : Nat) (hr : 5 ≤ r) (i k : Fin (4*r))
    (hs : 0 < sumIndex r i k) : 0 < tan (beta r i)+tan (beta r k) := by
  obtain ⟨ha,_,_⟩ := alpha_data r hr
  obtain ⟨hil,hih,_⟩ := beta_data r hr i
  obtain ⟨hkl,hkh,_⟩ := beta_data r hr k
  apply tangent_pair_sum_pos _ _ ⟨by linarith,by linarith⟩ ⟨by linarith,by linarith⟩
  rw [sum_angle r hr i k]
  exact mul_pos (by exact_mod_cast hs) ha

#print axioms beta_tan_strictMono
#print axioms sum_tangent
#print axioms factor_trigonometric
end Kobon.BBLGrid
