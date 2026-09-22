import Kobon.BBLRowGeometry

/-! The old-old cap side in each gap of the BBL auxiliary crossing model.
This proves one actual uncut side from the realized row order. A second
side, or an equivalent extremality argument, is still needed to conclude
that the cap replaces an old triangle.
-/
namespace Kobon.BBLCaps
open Finset Exterior BBLRowOrder BBLCount BBLTriangles BBLRowGeometry
set_option maxRecDepth 10000
set_option maxHeartbeats 10000000

def capRow (r j : Nat) : Nat :=
  if j=2*r-1 then 4*r
  else if j<2*r-1 then
    if j%2=0 then 3*r+j/2 else r+1+j/2
  else if j%2=0 then (j-2*r)/2 else 2*r+(j-2*r)/2

theorem capRow_le (r j : Nat) (hr : 1≤r) (hj : j<4*r-1) : capRow r j≤4*r := by
  unfold capRow
  split_ifs <;> omega

theorem capRow_central (r : Nat) (hr : 1≤r) : capRow r (2*r-1)=4*r := by
  simp [capRow]

theorem capRow_ne_horizontal (r j : Nat) (hr : 1≤r) (hj : j<4*r-1)
    (hc : j≠2*r-1) : capRow r j<4*r := by
  unfold capRow
  split_ifs <;> omega

theorem capRow_injective (r j l : Nat) (hr : 1≤r)
    (hj : j<4*r-1) (hl : l<4*r-1) (he : capRow r j=capRow r l) : j=l := by
  unfold capRow at he
  split_ifs at he <;> omega

theorem cap_no_aux_between (r j k : Nat) (hr : 1≤r) (hj : j<4*r-1)
    (hk : k≤4*r) (hne : capRow r j≠k) :
    newKey (2*r) (capRow r j) k≤oldKey j ∨
      oldKey (j+1)≤newKey (2*r) (capRow r j) k := by
  unfold capRow at *
  split_ifs at * <;> unfold newKey oldKey <;> push_cast <;> split_ifs <;> omega

theorem cap_side (r j : Nat) (hr : 1≤r) (hj : j<4*r-1)
    (L : Nat → Line ℝ) (w : Line ℝ) (horder : CrossingOrder r L w)
    (s : Fin (8*r+1)) (hne : s.val≠4*r+capRow r j) :
    Outside (projection w (intersection (L (4*r+capRow r j)) (L s)))
      (projection w (intersection (L (4*r+capRow r j)) (L j)))
      (projection w (intersection (L (4*r+capRow r j)) (L (j+1)))) := by
  have hi := capRow_le r j hr hj
  have hside :
      (crossKey r (capRow r j) s≤oldKey j ∧ crossKey r (capRow r j) s≤oldKey (j+1)) ∨
      (oldKey j≤crossKey r (capRow r j) s ∧ oldKey (j+1)≤crossKey r (capRow r j) s) := by
    by_cases hs : s.val<4*r
    · simp only [crossKey,if_pos hs,oldKey]
      by_cases hl : s.val≤j
      · left; constructor <;> push_cast <;> omega
      · right; constructor <;> push_cast <;> omega
    · simp only [crossKey,if_neg hs]
      have hh := cap_no_aux_between r j (s.val-4*r) hr hj (by omega) (by omega)
      have hsub : ((s.val-4*r : Nat) : Int)=(s.val:Int)-4*(r:Int) := by omega
      rw [hsub] at hh
      have hkeys : oldKey j≤oldKey (j+1) := by unfold oldKey; push_cast; omega
      rcases hh with hh | hh
      · exact Or.inl ⟨hh,le_trans hh hkeys⟩
      · exact Or.inr ⟨le_trans hkeys hh,hh⟩
  let a : Fin (8*r+1) := ⟨j,by omega⟩
  let b : Fin (8*r+1) := ⟨j+1,by omega⟩
  have ha : a.val≠4*r+capRow r j := by dsimp [a]; omega
  have hb : b.val≠4*r+capRow r j := by dsimp [b]; omega
  have hka : crossKey r (capRow r j) a=oldKey j := by simp [crossKey,a,show j<4*r by omega]
  have hkb : crossKey r (capRow r j) b=oldKey (j+1) := by simp [crossKey,b,show j+1<4*r by omega]
  rcases hside with ⟨h1,h2⟩ | ⟨h1,h2⟩
  · exact Or.inl ⟨horder _ hi s a hne ha (by simpa only [hka] using h1),
      horder _ hi s b hne hb (by simpa only [hkb] using h2)⟩
  · exact Or.inr ⟨horder _ hi a s ha hne (by simpa only [hka] using h1),
      horder _ hi b s hb hne (by simpa only [hkb] using h2)⟩

#print axioms cap_no_aux_between
#print axioms cap_side
end Kobon.BBLCaps
