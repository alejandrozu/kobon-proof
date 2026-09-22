import Kobon.BBLGridCuts
import Kobon.BBLPencilLimits
import Kobon.BBLLiftedKeys

/-! Actual interval profiles of every new-new BBL crossing.
This is the main trigonometric realization lemma for the integer row model. -/
namespace Kobon.BBLPencilProfiles
open Real BBLAnalytic BBLGrid BBLGridCuts BBLIntersection BBLPencilLimits
  BBLProfiles BBLRowOrder BBLLiftedKeys Filter
open scoped Topology
set_option maxRecDepth 10000
set_option maxHeartbeats 10000000

def LeftShift (r : Nat) (i k : Fin (4*r)) : Prop :=
  ((i.val:Int) < 2*(r:Int) ∧ (k.val:Int) < 2*(r:Int)) ∨
  ((((i.val:Int) < 2*(r:Int) ∧ 2*(r:Int) ≤ (k.val:Int)) ∨
    ((k.val:Int) < 2*(r:Int) ∧ 2*(r:Int) ≤ (i.val:Int))) ∧ 0 < sumIndex r i k)

instance (r : Nat) (i k : Fin (4*r)) : Decidable (LeftShift r i k) := by
  unfold LeftShift
  infer_instance

theorem key_anchor (r : Nat) (hr : 5 ≤ r) (i k : Fin (4*r))
    (h0 : sumIndex r i k ≠ 0) (hn : sumIndex r i k ≠ -2*(r:Int))
    (hp : sumIndex r i k ≠ 2*(r:Int)) :
    liftedNewKey (2*(r:Int)) i.val k.val =
      4*oldAnchor r (reducedIndex r (sumIndex r i k)) + (if LeftShift r i k then 1 else 3) := by
  have hi := i.isLt
  have hk := k.isLt
  have hh := lifted_anchor (2*(r:Int)) i.val k.val (by omega) (by omega) (by omega)
    (by omega) (by omega) (by simpa [sumIndex, ←mul_assoc] using h0)
    (by simpa [sumIndex, ←mul_assoc] using hn) (by simpa [sumIndex, ←mul_assoc] using hp)
  simpa [LeftShift,oldAnchor,keyOldAnchor,reducedIndex,reducedKeyIndex,sumIndex,
    show (2:ℤ)*(2*(r:Int)) = 4*(r:Int) by ring] using hh

theorem shift_sign (r : Nat) (hr : 5 ≤ r) (i k : Fin (4*r)) (h0 : sumIndex r i k ≠ 0) :
    (LeftShift r i k → (tan (beta r i)+tan (beta r k))*(tan (beta r i)*tan (beta r k)) < 0) ∧
    (¬LeftShift r i k → 0 < (tan (beta r i)+tan (beta r k))*(tan (beta r i)*tan (beta r k))) := by
  have ineg : (i.val:Int) < 2*(r:Int) → tan (beta r i) < 0 := by
    intro h
    exact beta_tan_negative r hr i (by exact_mod_cast h)
  have ipos : 2*(r:Int) ≤ (i.val:Int) → 0 < tan (beta r i) := by
    intro h
    exact beta_tan_positive r hr i (by exact_mod_cast h)
  have kneg : (k.val:Int) < 2*(r:Int) → tan (beta r k) < 0 := by
    intro h
    exact beta_tan_negative r hr k (by exact_mod_cast h)
  have kpos : 2*(r:Int) ≤ (k.val:Int) → 0 < tan (beta r k) := by
    intro h
    exact beta_tan_positive r hr k (by exact_mod_cast h)
  constructor
  · intro hs
    rcases hs with ⟨hi,hk⟩ | ⟨hmix,hs⟩
    · exact mul_neg_of_neg_of_pos (add_neg (ineg hi) (kneg hk))
        (mul_pos_of_neg_of_neg (ineg hi) (kneg hk))
    · have hsum := sum_tan_positive r hr i k hs
      rcases hmix with ⟨hi,hk⟩ | ⟨hk,hi⟩
      · exact mul_neg_of_pos_of_neg hsum (mul_neg_of_neg_of_pos (ineg hi) (kpos hk))
      · exact mul_neg_of_pos_of_neg hsum (mul_neg_of_pos_of_neg (ipos hi) (kneg hk))
  · intro hs
    by_cases hi : (i.val:Int) < 2*(r:Int)
    · by_cases hk : (k.val:Int) < 2*(r:Int)
      · exact (hs (Or.inl ⟨hi,hk⟩)).elim
      · have hk' : 2*(r:Int) ≤ (k.val:Int) := by omega
        have hsumidx : sumIndex r i k < 0 := by
          by_contra hh
          apply hs
          exact Or.inr ⟨Or.inl ⟨hi,hk'⟩,by omega⟩
        exact mul_pos_of_neg_of_neg (sum_tan_negative r hr i k hsumidx)
          (mul_neg_of_neg_of_pos (ineg hi) (kpos hk'))
    · have hi' : 2*(r:Int) ≤ (i.val:Int) := by omega
      by_cases hk : (k.val:Int) < 2*(r:Int)
      · have hsumidx : sumIndex r i k < 0 := by
          by_contra hh
          apply hs
          exact Or.inr ⟨Or.inr ⟨hk,hi'⟩,by omega⟩
        exact mul_pos_of_neg_of_neg (sum_tan_negative r hr i k hsumidx)
          (mul_neg_of_pos_of_neg (ipos hi') (kneg hk))
      · have hk' : 2*(r:Int) ≤ (k.val:Int) := by omega
        exact mul_pos (add_pos (ipos hi') (kpos hk')) (mul_pos (ipos hi') (kpos hk'))

theorem pair_profile_eventually (r : Nat) (hr : 5 ≤ r) (ε : ℝ)
    (hε0 : 0 < ε) (hε : ε < tan (alpha r/2)) (i k : Fin (4*r)) (hik : i ≠ k) :
    ∀ᶠ δ in 𝓝 (0:ℝ), 0 < δ →
      Profile (8*(r:Int)) (cut r ε) (liftedNewKey (2*(r:Int)) i.val k.val)
        (pairX δ (tan (beta r i)) (tan (beta r k))) := by
  have hi := i.isLt
  have hk := k.isLt
  have his : (0:ℤ) ≤ i.val := by omega
  have hks : (0:ℤ) ≤ k.val := by omega
  by_cases hn : sumIndex r i k = -2*(r:Int)
  · have hp := tangent_product_complementary r hr i k (Or.inl hn)
    have hsum := sum_tan_negative r hr i k (by rw [hn]; omega)
    have hkey : liftedNewKey (2*(r:Int)) i.val k.val = 16*(r:Int)+1 := by
      have hcomp : NegativeComplement (2*(r:Int)) i.val k.val := by
        unfold NegativeComplement
        unfold sumIndex at hn
        omega
      rw [liftedNewKey,if_pos hcomp]
      ring
    apply (complementary_far_right _ _ (cut r ε (8*(r:Int))) hp hsum).mono
    intro δ hδ hδp
    exact Or.inr (Or.inl ⟨by rw [hkey]; ring,hδ hδp⟩)
  by_cases hp : sumIndex r i k = 2*(r:Int)
  · have hprod := tangent_product_complementary r hr i k (Or.inr hp)
    have hsum := sum_tan_positive r hr i k (by rw [hp]; omega)
    have hkey : liftedNewKey (2*(r:Int)) i.val k.val = -1 := by
      unfold liftedNewKey NegativeComplement newKey
      unfold sumIndex at hp
      split_ifs <;> omega
    apply (complementary_far_left _ _ (cut r ε 0) hprod hsum).mono
    intro δ hδ hδp
    exact Or.inl ⟨hkey,hδ hδp⟩
  by_cases h0 : sumIndex r i k = 0
  · have hsum := sum_angle r hr i k
    rw [h0] at hsum
    have hb : beta r i = -beta r k := by norm_num at hsum; linarith
    have hts : tan (beta r i)+tan (beta r k) = 0 := by rw [hb,tan_neg]; ring
    have hkey : liftedNewKey (2*(r:Int)) i.val k.val = 8*(r:Int) := by
      unfold liftedNewKey NegativeComplement newKey
      unfold sumIndex at h0
      split_ifs <;> omega
    apply Filter.Eventually.of_forall
    intro δ _
    right; right; left
    refine ⟨4*(r:Int),by omega,by omega,by rw [hkey]; ring,?_⟩
    simp [pairX,hts,cut_zero]
  have hsb := sum_index_bounds r i k hik
  have hsb' : -4*(r:Int) < sumIndex r i k ∧ sumIndex r i k < 4*(r:Int) := by omega
  have hz0 : reducedIndex r (sumIndex r i k) ≠ 0 := by
    unfold reducedIndex
    split_ifs <;> omega
  have ha := anchor_bounds r _ (reduced_bounds r _ hsb' hn hp) hz0
  have htarget := rational_sum_anchor r hr ε i k hik hn hp hz0
  have hti := beta_tan_ne_zero r hr i
  have htk := beta_tan_ne_zero r hr k
  have hcomp := tangent_product_noncomplementary r hr i k hik hn hp
  have hlim := pairX_tendsto _ _ hti htk hcomp
  rw [htarget] at hlim
  have hkey := key_anchor r hr i k h0 hn hp
  have hcuts := cut_increasing r hr ε hε0 hε
  by_cases hs : LeftShift r i k
  · have hside := crossing_left_eventually _ _ hti htk hcomp ((shift_sign r hr i k h0).1 hs)
    rw [htarget] at hside
    have heq : liftedNewKey (2*(r:Int)) i.val k.val =
        2*(2*oldAnchor r (reducedIndex r (sumIndex r i k))+1)-1 := by
      rw [hkey,if_pos hs]
      ring
    rw [heq]
    exact profile_left_eventually _ _ hcuts _ (by omega) (by omega) _ hlim hside
  · have hside := crossing_right_eventually _ _ hti htk hcomp ((shift_sign r hr i k h0).2 hs)
    rw [htarget] at hside
    have heq : liftedNewKey (2*(r:Int)) i.val k.val =
        2*(2*oldAnchor r (reducedIndex r (sumIndex r i k))+1)+1 := by
      rw [hkey,if_neg hs]
      ring
    rw [heq]
    exact profile_right_eventually _ _ hcuts _ (by omega) (by omega) _ hlim hside

#print axioms pair_profile_eventually
end Kobon.BBLPencilProfiles
