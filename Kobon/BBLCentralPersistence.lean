import Kobon.BBLCentralEnvelope
import Kobon.BBLCapReplacement
import Kobon.Reindex

/-! The central old triangle is retained on Y0. Only its two endpoint
tests require the row order; its apex tests follow from continuity. -/
namespace Kobon.BBLCentralPersistence
open Exterior HybridBoundary BBLExtrema BBLTriangles BBLRowGeometry BBLCentralEnvelope
  BBLPersistence BBLCapReplacement Filter
open scoped Topology
set_option maxHeartbeats 10000000

def CentralEndpointSigns (n m i j : Nat) (L D : Nat → Line ℝ) (κ : ℝ) : Prop :=
  let v := orientedEval (L 0) (L i) (L j)
  ∀ s : Fin m,
    0 ≤ v*orientedEval (perturb (L 0) (D s) κ) (L 0) (L i) ∧
    0 ≤ v*orientedEval (perturb (L 0) (D s) κ) (L 0) (L j)

theorem central_retained_eventually (n m i j : Nat) (L D : Nat → Line ℝ)
    (hp : NoParallel n L) (ht : TrianglePredicate n L ⟨0,i,j⟩) :
    ∀ᶠ κ in 𝓝 (0:ℝ), CentralEndpointSigns n m i j L D κ →
      TrianglePredicate (n+m) (pencilAppend n L D 0 κ) ⟨0,i,j⟩ := by
  have hi : 0 < i := ht.1
  have hij : i < j := ht.2.1
  have hjn : j < n := ht.2.2.1
  have hin : i < n := by omega
  have hzn : 0 < n := by omega
  let v := orientedEval (L 0) (L i) (L j)
  have hev : evalVertex (L 0) (L i) (L j) ≠ 0 := by
    rw [eval_cyclic]
    exact ht.2.2.2.1
  have hv : v ≠ 0 := mul_ne_zero hev (hp ⟨i,hin⟩ ⟨j,hjn⟩ hij)
  have hapex : ∀ᶠ κ in 𝓝 (0:ℝ), ∀ s : Fin m,
      0 < v*orientedEval (perturb (L 0) (D s) κ) (L i) (L j) := by
    apply Filter.eventually_all.mpr
    intro s
    exact apex_test_eventually _ _ _ _ hv
  apply hapex.mono
  intro κ ha he
  refine ⟨hi,hij,by change j < n+m; omega,?_,?_⟩
  · simpa only [pencilAppend,if_pos hzn,if_pos hin,if_pos hjn] using ht.2.2.2.1
  · intro s
    simp only [pencilAppend,if_pos hzn,if_pos hin,if_pos hjn]
    by_cases hsn : s.val < n
    · rw [if_pos hsn]
      exact ht.2.2.2.2 ⟨s.val,hsn⟩
    · rw [if_neg hsn]
      have hsm : s.val-n < m := by omega
      have hend := he ⟨s.val-n,hsm⟩
      exact weakSigns_aligned v _ _ _ hv hend.1 hend.2 (le_of_lt (ha ⟨s.val-n,hsm⟩))

def CanonicalCentralSigns (r : Nat) (L : Nat → Line ℝ) : Prop :=
  let v := orientedEval (L (8*r)) (L (2*r-1)) (L (2*r))
  ∀ k < 4*r,
    0 ≤ v*orientedEval (L (4*r+k)) (L (8*r)) (L (2*r-1)) ∧
    0 ≤ v*orientedEval (L (4*r+k)) (L (8*r)) (L (2*r))

theorem canonical_central_signs (r : Nat) (hr : 1 ≤ r)
    (L : Nat → Line ℝ) (w : Line ℝ) (m a : Nat → ℝ)
    (hp : NoParallel (8*r+1) L) (horder : CrossingOrder r L w)
    (hgraph : ∀ t < 4*r, L (4*r+t)=graphLine (m t) (a t))
    (hzero : L (8*r)=graphLine 0 0)
    (hmneg : ∀ t < 2*r, m t < 0) (hmpos : ∀ t, 2*r ≤ t → t < 4*r → 0 < m t)
    (hdir : 0 < w.a)
    (hapex : 0 < (intersection (L (2*r-1)) (L (2*r))).2) :
    CanonicalCentralSigns r L := by
  have hdA := hp ⟨2*r-1,by omega⟩ ⟨2*r,by omega⟩ (show 2*r-1 < 2*r by omega)
  have hdL : det (L (8*r)) (L (2*r-1)) ≠ 0 := by
    rw [det_skew]
    exact neg_ne_zero.mpr (hp ⟨2*r-1,by omega⟩ ⟨8*r,by omega⟩ (show 2*r-1 < 8*r by omega))
  have hdR : det (L (8*r)) (L (2*r)) ≠ 0 := by
    rw [det_skew]
    exact neg_ne_zero.mpr (hp ⟨2*r,by omega⟩ ⟨8*r,by omega⟩ (show 2*r < 8*r by omega))
  have hv : orientedEval (L (8*r)) (L (2*r-1)) (L (2*r)) ≤ 0 := by
    rw [oriented_nonpos_iff _ _ _ hdA,hzero]
    simp only [affineEval,graphLine,zero_mul,neg_mul,one_mul,sub_zero,zero_add]
    linarith
  intro k hk
  have hl := central_endpoint r (2*r-1) k hr (Or.inl rfl) hk L w m a hp horder
    hgraph hzero hmneg hmpos hdir
  have hr' := central_endpoint r (2*r) k hr (Or.inr rfl) hk L w m a hp horder
    hgraph hzero hmneg hmpos hdir
  exact ⟨mul_nonneg_of_nonpos_of_nonpos hv ((oriented_nonpos_iff _ _ _ hdL).mpr hl),
    mul_nonneg_of_nonpos_of_nonpos hv ((oriented_nonpos_iff _ _ _ hdR).mpr hr')⟩

theorem centralSigns_of_canonical (r : Nat) (hr : 1 ≤ r)
    (old D : Nat → Line ℝ) (κ : ℝ)
    (he : CanonicalCentralSigns r
      (Reindex.rotate (8*r+1) (pencilAppend (4*r+1) old D 0 κ))) :
    CentralEndpointSigns (4*r+1) (4*r) (2*r) (2*r+1) old D κ := by
  let raw := pencilAppend (4*r+1) old D 0 κ
  let L := Reindex.rotate (8*r+1) raw
  have hrot (t : Nat) (ht : t+1 < 8*r+1) : L t=raw (t+1) := by
    simp [L,Reindex.rotate,Reindex.shift,ht]
  have hlast : L (8*r)=old 0 := by simp [L,raw,Reindex.rotate,Reindex.shift,pencilAppend]
  have hlo : L (2*r-1)=old (2*r) := by
    rw [hrot (2*r-1) (by omega)]
    have hid : 2*r-1+1=2*r := by omega
    rw [hid]
    simp [raw,pencilAppend,show 2*r < 4*r+1 by omega]
  have hhi : L (2*r)=old (2*r+1) := by
    rw [hrot (2*r) (by omega)]
    simp [raw,pencilAppend,show 2*r+1 < 4*r+1 by omega]
  change CanonicalCentralSigns r L at he
  intro s
  have hM : L (4*r+s.val)=perturb (old 0) (D s) κ := by
    rw [hrot (4*r+s.val) (by omega)]
    have hid : 4*r+s.val+1=(4*r+1)+s.val := by omega
    rw [hid]
    simp [raw,pencilAppend,show ¬(4*r+1+s.val < 4*r+1) by omega]
  have hh := he s.val s.isLt
  simpa only [hlast,hlo,hhi,hM] using hh

#print axioms central_retained_eventually
#print axioms canonical_central_signs
#print axioms centralSigns_of_canonical

theorem central_replaced_eventually (r : Nat) (hr : 1 ≤ r) (old D : Nat → Line ℝ)
    (hp : NoParallel (4*r+1) old)
    (ht : TrianglePredicate (4*r+1) old ⟨0,2*r,2*r+1⟩) :
    ∀ᶠ κ in 𝓝 (0:ℝ),
      CanonicalCentralSigns r
        (Reindex.rotate (8*r+1) (pencilAppend (4*r+1) old D 0 κ)) →
      TrianglePredicate (8*r+1)
        (Reindex.rotate (8*r+1) (pencilAppend (4*r+1) old D 0 κ))
        ⟨2*r-1,2*r,8*r⟩ := by
  have hh := central_retained_eventually (4*r+1) (4*r) (2*r) (2*r+1) old D hp ht
  apply hh.mono
  intro κ hκ he
  have hraw := hκ (centralSigns_of_canonical r hr old D κ he)
  have hN : 4*r+1+4*r=8*r+1 := by omega
  rw [hN] at hraw
  have hrot := Reindex.rotate_zero_triangle (8*r+1) (2*r) (2*r+1)
    (pencilAppend (4*r+1) old D 0 κ) hraw
  simpa only [Nat.add_sub_cancel_right] using hrot

#print axioms central_replaced_eventually
end Kobon.BBLCentralPersistence
