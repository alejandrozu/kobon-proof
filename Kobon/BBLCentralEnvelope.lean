import Kobon.BBLCapEnvelope

/-! Every added BBL line lies below the two horizontal vertices of the
central old triangle, as a direct consequence of the crossing order. -/
namespace Kobon.BBLCentralEnvelope
open Exterior HybridBoundary BBLExtrema BBLTriangles BBLRowOrder BBLRowGeometry
  BBLCaps BBLCapSigns BBLCapEnvelope
set_option maxHeartbeats 10000000

theorem central_endpoint (r s k : Nat) (hr : 1 ≤ r)
    (hs : s=2*r-1 ∨ s=2*r) (hk : k < 4*r)
    (L : Nat → Line ℝ) (w : Line ℝ) (m a : Nat → ℝ)
    (hp : NoParallel (8*r+1) L) (horder : CrossingOrder r L w)
    (hgraph : ∀ t < 4*r, L (4*r+t)=graphLine (m t) (a t))
    (hzero : L (8*r)=graphLine 0 0)
    (hmneg : ∀ t < 2*r, m t < 0) (hmpos : ∀ t, 2*r ≤ t → t < 4*r → 0 < m t)
    (hdir : 0 < w.a) :
    affineEval (L (4*r+k)) (intersection (L (8*r)) (L s)) ≤ 0 := by
  have hsn : s < 4*r := by omega
  let u : Fin (8*r+1) := ⟨8*r,by omega⟩
  let v : Fin (8*r+1) := ⟨s,by omega⟩
  let z : Fin (8*r+1) := ⟨4*r+k,by omega⟩
  have huv : u ≠ v := by intro h; have := congrArg Fin.val h; dsimp [u,v] at this; omega
  have hd := det_ne_of_ne _ L hp u v huv
  have hkm : m k ≠ 0 := by
    by_cases hkn : k < 2*r
    · exact ne_of_lt (hmneg k hkn)
    · exact ne_of_gt (hmpos k (by omega) hk)
  let P := intersection (L (8*r)) (L s)
  have hPon : affineEval (graphLine 0 0) P=0 := by
    rw [←hzero]
    exact intersection_on_left _ _ hd
  have hQon : affineEval (graphLine 0 0) (a k,0)=0 := by
    simp [affineEval,graphLine]
  have hPy : P.2=0 := by simpa [affineEval,graphLine] using hPon
  have hZ : intersection (L (8*r)) (L (4*r+k))=(a k,0) := by
    rw [intersection_swap,hgraph k hk,hzero,graph_horizontal_intersection _ _ hkm]
  have hK : crossKey r (4*r) v=oldKey s := by simp [crossKey,v,hsn]
  have hH : crossKey r (4*r) z=horizontalKey r k := by
    have hcast : crossKey r (4*r) z=newKey (2*r) (4*r) k := by
      dsimp [crossKey,z]
      rw [if_neg (by omega)]
      congr 1 <;> push_cast <;> ring
    rw [hcast]
    unfold newKey horizontalKey
    push_cast
    split_ifs <;> omega
  have hv : v.val ≠ 4*r+4*r := by dsimp [v]; omega
  have hz : z.val ≠ 4*r+4*r := by dsimp [z]; omega
  have hdir' : 0 < w.a+w.b*0 := by simpa using hdir
  change affineEval (L (4*r+k)) P ≤ 0
  rw [hgraph k hk]
  change m k*P.1 + (-1)*P.2-m k*a k ≤ 0
  rw [hPy]
  by_cases hkn : k < 2*r
  · have hm := hmneg k hkn
    have hkey : horizontalKey r k ≤ oldKey s := by
      unfold horizontalKey oldKey
      rw [if_pos hkn]
      omega
    have ho := horder (4*r) (le_refl _) z v hz hv (by rw [hH,hK]; exact hkey)
    have hsum : 4*r+4*r=8*r := by omega
    rw [hsum] at ho
    change projection w (intersection (L (8*r)) (L (4*r+k))) ≤ projection w P at ho
    rw [hZ] at ho
    have hx := graph_projection_order 0 0 w (a k,0) P hQon hPon hdir' ho
    have hy := mul_nonpos_of_nonpos_of_nonneg (le_of_lt hm) (sub_nonneg.mpr hx)
    nlinarith only [hy]
  · have hkn' : 2*r ≤ k := by omega
    have hm := hmpos k hkn' hk
    have hkey : oldKey s ≤ horizontalKey r k := by
      unfold horizontalKey oldKey
      rw [if_neg hkn]
      omega
    have ho := horder (4*r) (le_refl _) v z hv hz (by rw [hK,hH]; exact hkey)
    have hsum : 4*r+4*r=8*r := by omega
    rw [hsum] at ho
    change projection w P ≤ projection w (intersection (L (8*r)) (L (4*r+k))) at ho
    rw [hZ] at ho
    have hx := graph_projection_order 0 0 w P (a k,0) hPon hQon hdir' ho
    have hy := mul_nonpos_of_nonneg_of_nonpos (le_of_lt hm) (sub_nonpos.mpr hx)
    nlinarith only [hy]

#print axioms central_endpoint
end Kobon.BBLCentralEnvelope
