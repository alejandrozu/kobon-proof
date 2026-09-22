import Kobon.BBLRowGeometry

/-! Row maxima of the integer crossing model give actual visible wedges. -/
namespace Kobon.BBLRowMax
open Exterior HybridBoundary BBLExtrema BBLTriangles BBLRowOrder BBLRowGeometry
set_option maxHeartbeats 10000000
set_option maxRecDepth 10000

theorem row_bound_not_last (h i k : Int) (hh : 1 ≤ h)
    (hi : 0 ≤ i) (hi' : i < 2*h-1) (hk : 0 ≤ k) (hk' : k ≤ 2*h)
    (hik : i ≠ k) : newKey h i k ≤ 8*h-1 := by
  unfold newKey
  split_ifs <;> omega

theorem projection_ne (n : Nat) (L : Nat → Line ℝ) (w : Line ℝ)
    (hp : NoParallel n L) (hs : NoConcurrent n L) (hw : Admissible n L w)
    (i j k : Fin n) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    projection w (intersection (L i) (L j)) ≠
      projection w (intersection (L i) (L k)) := by
  have hdij := det_ne_of_ne n L hp i j hij
  have hdik := det_ne_of_ne n L hp i k hik
  have hdwi : det w (L i) ≠ 0 := by rw [det_skew]; exact neg_ne_zero.mpr (hw i)
  have hnd : evalVertex (L k) (L i) (L j) ≠ 0 := by
    rcases lt_or_gt_of_ne hij with h | h
    · exact no_concurrent_at_pair n L hs i j k h (Ne.symm hik) (Ne.symm hjk)
    · have heq : evalVertex (L k) (L i) (L j) = -evalVertex (L k) (L j) (L i) := by
        dsimp [evalVertex,vertex,det]
        ring
      rw [heq]
      exact neg_ne_zero.mpr (no_concurrent_at_pair n L hs j i k h (Ne.symm hjk) (Ne.symm hik))
  intro he
  have hv := evaluation_from_intersection (L k) (L i) (L j) w hdij hdik hdwi
  rw [he,sub_self,mul_zero,eval_intersection _ _ _ hdij] at hv
  exact (div_ne_zero hnd hdij) hv

theorem row_extremal (r i k : Nat) (L : Nat → Line ℝ) (w : Line ℝ)
    (hp : NoParallel (8*r+1) L) (hs : NoConcurrent (8*r+1) L)
    (hw : Admissible (8*r+1) L w) (horder : CrossingOrder r L w)
    (hi : i ≤ 4*r) (hk : k ≤ 4*r) (hik : i ≠ k)
    (hmax : ∀ s : Fin (8*r+1), s.val ≠ 4*r+i →
      crossKey r i s ≤ newKey (2*r) i k) :
    ∀ s : Fin (8*r+1), s.val ≠ 4*r+i → s.val ≠ 4*r+k →
      projection w (intersection (L (4*r+i)) (L s)) <
        projection w (intersection (L (4*r+i)) (L (4*r+k))) := by
  let u : Fin (8*r+1) := ⟨4*r+i,by omega⟩
  let v : Fin (8*r+1) := ⟨4*r+k,by omega⟩
  have hv : v.val ≠ 4*r+i := by dsimp [v]; omega
  have hkey : crossKey r i v=newKey (2*r) i k := by
    dsimp [crossKey,v]
    rw [if_neg (by omega)]
    congr 1 <;> omega
  intro s hsu hsv
  have hle := horder i hi s v hsu hv (by rw [hkey]; exact hmax s hsu)
  apply lt_of_le_of_ne hle
  have hus : u ≠ s := by intro h; have := congrArg Fin.val h; dsimp [u] at this; omega
  have huv : u ≠ v := by intro h; have := congrArg Fin.val h; dsimp [u,v] at this; omega
  have hsv' : s ≠ v := by intro h; have := congrArg Fin.val h; dsimp [v] at this; omega
  exact projection_ne _ L w hp hs hw u s v hus huv hsv'

theorem row_extremal_label (r i : Nat) (L : Nat → Line ℝ) (w : Line ℝ)
    (hp : NoParallel (8*r+1) L) (hs : NoConcurrent (8*r+1) L)
    (hw : Admissible (8*r+1) L w) (horder : CrossingOrder r L w)
    (hi : i ≤ 4*r) (v : Fin (8*r+1)) (hv : v.val ≠ 4*r+i)
    (hmax : ∀ s : Fin (8*r+1), s.val ≠ 4*r+i → crossKey r i s ≤ crossKey r i v) :
    ∀ s : Fin (8*r+1), s.val ≠ 4*r+i → s ≠ v →
      projection w (intersection (L (4*r+i)) (L s)) <
        projection w (intersection (L (4*r+i)) (L v)) := by
  let u : Fin (8*r+1) := ⟨4*r+i,by omega⟩
  intro s hsu hsv
  have hle := horder i hi s v hsu hv (hmax s hsu)
  apply lt_of_le_of_ne hle
  have hus : u ≠ s := by intro h; have := congrArg Fin.val h; dsimp [u] at this; omega
  have huv : u ≠ v := by intro h; have := congrArg Fin.val h; dsimp [u] at this; omega
  exact projection_ne _ L w hp hs hw u s v hus huv hsv

theorem max_pair_visible (r i k : Nat) (L : Nat → Line ℝ) (w : Line ℝ)
    (hp : NoParallel (8*r+1) L) (hs : NoConcurrent (8*r+1) L)
    (hw : Admissible (8*r+1) L w) (horder : CrossingOrder r L w)
    (hi : i ≤ 4*r) (hk : k ≤ 4*r) (hik : i < k)
    (himax : ∀ s : Fin (8*r+1), s.val ≠ 4*r+i →
      crossKey r i s ≤ newKey (2*r) i k)
    (hkmax : ∀ s : Fin (8*r+1), s.val ≠ 4*r+k →
      crossKey r k s ≤ newKey (2*r) k i) :
    VisiblePair (8*r+1) L w ⟨4*r+i,4*r+k,8*r+1⟩ := by
  apply extremal_visible _ L w hp hw _ (by dsimp; omega) (by dsimp; omega) rfl
  intro s hsi hsk
  constructor
  · exact row_extremal r i k L w hp hs hw horder hi hk (by omega) himax s hsi hsk
  · rw [intersection_swap (L (4*r+i)) (L (4*r+k))]
    exact row_extremal r k i L w hp hs hw horder hk hi (by omega) hkmax s hsk hsi

#print axioms max_pair_visible
end Kobon.BBLRowMax
