import Kobon.BBLLiftedKeys
import Kobon.BBLRowGeometry

/-! Interface between the analytic lifted cuts and the integer row model. -/
namespace Kobon.BBLLiftedRows
open BBLRowOrder BBLRowGeometry BBLLiftedKeys

def liftedCrossKey (r i label : Nat) : Int :=
  if label < 4*r then oldKey label else liftedNewKey (2*r) i (label-4*r)

theorem liftedCrossKey_le_iff (r i : Nat) (hr : 1 ≤ r) (hi : i ≤ 4*r)
    (a b : Fin (8*r+1)) (ha : a.val ≠ 4*r+i) (hb : b.val ≠ 4*r+i) :
    liftedCrossKey r i a ≤ liftedCrossKey r i b ↔ crossKey r i a ≤ crossKey r i b := by
  by_cases hao : a.val < 4*r
  · by_cases hbo : b.val < 4*r
    · simp only [liftedCrossKey,crossKey,if_pos hao,if_pos hbo]
    · simp only [liftedCrossKey,crossKey,if_pos hao,if_neg hbo]
      apply lifted_old_le_iff <;> omega
  · by_cases hbo : b.val < 4*r
    · simp only [liftedCrossKey,crossKey,if_neg hao,if_pos hbo]
      apply lifted_le_old_iff <;> omega
    · simp only [liftedCrossKey,crossKey,if_neg hao,if_neg hbo]
      apply lifted_new_le_iff <;> omega

theorem crossKey_injective (r i : Nat) (hr : 1 ≤ r) (hi : i ≤ 4*r)
    (a b : Fin (8*r+1)) (ha : a.val ≠ 4*r+i) (hb : b.val ≠ 4*r+i)
    (he : crossKey r i a=crossKey r i b) : a=b := by
  by_cases hao : a.val < 4*r
  · by_cases hbo : b.val < 4*r
    · simp only [crossKey,if_pos hao,if_pos hbo,oldKey] at he
      apply Fin.ext
      omega
    · simp only [crossKey,if_pos hao,if_neg hbo] at he
      exact False.elim ((newKey_ne_oldKey (2*r) i ((b.val:Int)-4*r) a.val) he.symm)
  · by_cases hbo : b.val < 4*r
    · simp only [crossKey,if_neg hao,if_pos hbo] at he
      exact False.elim ((newKey_ne_oldKey (2*r) i ((a.val:Int)-4*r) b.val) he)
    · simp only [crossKey,if_neg hao,if_neg hbo] at he
      have hh := newKey_injective (2*r) i ((a.val:Int)-4*r) ((b.val:Int)-4*r)
        (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) he
      apply Fin.ext
      omega

theorem liftedCrossKey_injective (r i : Nat) (hr : 1 ≤ r) (hi : i ≤ 4*r)
    (a b : Fin (8*r+1)) (ha : a.val ≠ 4*r+i) (hb : b.val ≠ 4*r+i)
    (he : liftedCrossKey r i a=liftedCrossKey r i b) : a=b := by
  apply crossKey_injective r i hr hi a b ha hb
  apply le_antisymm
  · exact (liftedCrossKey_le_iff r i hr hi a b ha hb).mp (le_of_eq he)
  · exact (liftedCrossKey_le_iff r i hr hi b a hb ha).mp (le_of_eq he.symm)

#print axioms liftedCrossKey_le_iff
#print axioms liftedCrossKey_injective
end Kobon.BBLLiftedRows
