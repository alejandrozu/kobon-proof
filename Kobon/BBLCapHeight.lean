import Kobon.BBLCapEnvelope

/-! The cap lies on the same side of the distinguished horizontal line
as the old apex. This follows from row order and the slope orientation. -/
namespace Kobon.BBLCapHeight
open Exterior HybridBoundary BBLExtrema BBLTriangles BBLRowOrder BBLRowGeometry
  BBLCaps BBLCapSigns BBLCapEnvelope
set_option maxRecDepth 10000
set_option maxHeartbeats 10000000

theorem cap_key_height (r j s : Nat) (hr : 1 ≤ r) (hj : j < 4*r-1)
    (hc : j ≠ 2*r-1) (hs : s=j ∨ s=j+1) :
    (capRow r j < 2*r →
      (j%2=0 → horizontalKey r (capRow r j) ≤ oldKey s) ∧
      (j%2≠0 → oldKey s ≤ horizontalKey r (capRow r j))) ∧
    (2*r ≤ capRow r j →
      (j%2=0 → oldKey s ≤ horizontalKey r (capRow r j)) ∧
      (j%2≠0 → horizontalKey r (capRow r j) ≤ oldKey s)) := by
  unfold capRow at *
  split_ifs at * <;> unfold horizontalKey oldKey <;> push_cast <;> split_ifs <;> omega

theorem cap_endpoint_height (r j s : Nat) (hr : 1 ≤ r) (hj : j < 4*r-1)
    (hc : j ≠ 2*r-1) (hs : s=j ∨ s=j+1)
    (L : Nat → Line ℝ) (w : Line ℝ) (m a : Nat → ℝ)
    (hp : NoParallel (8*r+1) L) (horder : CrossingOrder r L w)
    (hgraph : ∀ t < 4*r, L (4*r+t)=graphLine (m t) (a t))
    (hzero : L (8*r)=graphLine 0 0)
    (hmneg : ∀ t < 2*r, m t < 0) (hmpos : ∀ t, 2*r ≤ t → t < 4*r → 0 < m t)
    (hdir : 0 < w.a+w.b*m (capRow r j)) :
    (j%2=0 → 0 ≤ affineEval (L (8*r))
      (intersection (L (4*r+capRow r j)) (L s))) ∧
    (j%2≠0 → affineEval (L (8*r))
      (intersection (L (4*r+capRow r j)) (L s)) ≤ 0) := by
  let i := capRow r j
  have hi : i < 4*r := capRow_ne_horizontal r j hr hj hc
  have hsn : s < 4*r := by omega
  let u : Fin (8*r+1) := ⟨4*r+i,by omega⟩
  let v : Fin (8*r+1) := ⟨s,by omega⟩
  let z : Fin (8*r+1) := ⟨8*r,by omega⟩
  have huv : u ≠ v := by intro h; have := congrArg Fin.val h; dsimp [u,v] at this; omega
  have hd := det_ne_of_ne _ L hp u v huv
  have him : m i ≠ 0 := by
    by_cases hin : i < 2*r
    · exact ne_of_lt (hmneg i hin)
    · exact ne_of_gt (hmpos i (by omega) hi)
  let P := intersection (L (4*r+i)) (L s)
  have hPon : affineEval (graphLine (m i) (a i)) P=0 := by
    rw [←hgraph i hi]
    exact intersection_on_left _ _ hd
  have hQon : affineEval (graphLine (m i) (a i)) (a i,0)=0 := by
    dsimp [affineEval,graphLine]; ring
  have hY : P.2=m i*(P.1-a i) := by
    dsimp [affineEval,graphLine] at hPon
    linarith
  have hZ : intersection (L (4*r+i)) (L (8*r))=(a i,0) := by
    rw [hgraph i hi,hzero,graph_horizontal_intersection _ _ him]
  have hK : crossKey r i v=oldKey s := by simp [crossKey,v,hsn]
  have hH : crossKey r i z=horizontalKey r i := by
    have hcast : crossKey r i z=newKey (2*r) i (4*r) := by
      dsimp [crossKey,z]
      rw [if_neg (by omega)]
      congr 1 <;> push_cast <;> ring
    rw [hcast,horizontalKey_eq r i hi]
  have hv : v.val ≠ 4*r+i := by dsimp [v]; omega
  have hz : z.val ≠ 4*r+i := by dsimp [z]; omega
  have hleft : oldKey s ≤ horizontalKey r i → P.1 ≤ a i := by
    intro hh
    have ho := horder i (le_of_lt hi) v z hv hz (by rw [hK,hH]; exact hh)
    change projection w P ≤ projection w (intersection (L (4*r+i)) (L (8*r))) at ho
    rw [hZ] at ho
    exact graph_projection_order _ _ w P (a i,0) hPon hQon hdir ho
  have hright : horizontalKey r i ≤ oldKey s → a i ≤ P.1 := by
    intro hh
    have ho := horder i (le_of_lt hi) z v hz hv (by rw [hH,hK]; exact hh)
    change projection w (intersection (L (4*r+i)) (L (8*r))) ≤ projection w P at ho
    rw [hZ] at ho
    exact graph_projection_order _ _ w (a i,0) P hQon hPon hdir ho
  have hkeys := cap_key_height r j s hr hj hc hs
  change (j%2=0 → 0 ≤ affineEval (L (8*r)) P) ∧
    (j%2≠0 → affineEval (L (8*r)) P ≤ 0)
  rw [hzero]
  simp only [affineEval,graphLine,zero_mul,neg_mul,one_mul,sub_zero,zero_add]
  by_cases hin : i < 2*r
  · have hm := hmneg i hin
    obtain ⟨hke,hko⟩ := hkeys.1 hin
    constructor
    · intro he
      have hx := hright (hke he)
      have hy := mul_nonpos_of_nonpos_of_nonneg (le_of_lt hm) (sub_nonneg.mpr hx)
      linarith
    · intro ho
      have hx := hleft (hko ho)
      have hy := mul_nonneg_of_nonpos_of_nonpos (le_of_lt hm) (sub_nonpos.mpr hx)
      linarith
  · have hin' : 2*r ≤ i := by omega
    have hm := hmpos i hin' hi
    obtain ⟨hke,hko⟩ := hkeys.2 hin'
    constructor
    · intro he
      have hx := hleft (hke he)
      have hy := mul_nonpos_of_nonneg_of_nonpos (le_of_lt hm) (sub_nonpos.mpr hx)
      linarith
    · intro ho
      have hx := hright (hko ho)
      have hy := mul_nonneg (le_of_lt hm) (sub_nonneg.mpr hx)
      linarith

#print axioms cap_endpoint_height
end Kobon.BBLCapHeight
