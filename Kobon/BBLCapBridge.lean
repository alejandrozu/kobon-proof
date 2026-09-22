import Kobon.BBLCapHeight
import Kobon.BBLCapReplacement
import Kobon.Reindex

/-! Cap endpoint signs in the orientation convention used by the continuity
replacement theorem. All signs are derived from the actual crossing rows. -/
namespace Kobon.BBLCapBridge
open Exterior HybridBoundary BBLExtrema BBLTriangles BBLRowGeometry BBLCaps
  BBLCapEnvelope BBLCapHeight BBLPersistence BBLCapReplacement
set_option maxHeartbeats 10000000

def CanonicalEndpointSigns (r j : Nat) (L : Nat → Line ℝ) : Prop :=
  let M := L (4*r+capRow r j)
  let v := orientedEval (L (8*r)) (L j) (L (j+1))
  ∀ s : Fin (8*r+1), 4*r ≤ s.val →
    0 ≤ v*orientedEval (L s) (L j) M ∧
    0 ≤ v*orientedEval (L s) (L (j+1)) M

theorem canonical_endpoint_signs (r j : Nat) (hr : 1 ≤ r) (hj : j < 4*r-1)
    (hc : j ≠ 2*r-1) (L : Nat → Line ℝ) (w : Line ℝ) (m a : Nat → ℝ)
    (hp : NoParallel (8*r+1) L) (hs : NoConcurrent (8*r+1) L)
    (hw : Admissible (8*r+1) L w) (horder : CrossingOrder r L w)
    (hgraph : ∀ t < 4*r, L (4*r+t)=graphLine (m t) (a t))
    (hzero : L (8*r)=graphLine 0 0)
    (hmneg : ∀ t < 2*r, m t < 0) (hmpos : ∀ t, 2*r ≤ t → t < 4*r → 0 < m t)
    (ha : ∀ s t, s < t → t < 4*r → a s < a t)
    (hdir : 0 < w.a+w.b*m (capRow r j))
    (hapex : (j%2=0 → (intersection (L j) (L (j+1))).2 < 0) ∧
      (j%2≠0 → 0 < (intersection (L j) (L (j+1))).2)) :
    CanonicalEndpointSigns r j L := by
  let i := capRow r j
  have hi : i < 4*r := capRow_ne_horizontal r j hr hj hc
  have hdA := hp ⟨j,by omega⟩ ⟨j+1,by omega⟩ (show j < j+1 by omega)
  have hdL := hp ⟨j,by omega⟩ ⟨4*r+i,by omega⟩ (show j < 4*r+i by omega)
  have hdR := hp ⟨j+1,by omega⟩ ⟨4*r+i,by omega⟩ (show j+1 < 4*r+i by omega)
  have hv : (j%2=0 → 0 ≤ orientedEval (L (8*r)) (L j) (L (j+1))) ∧
      (j%2≠0 → orientedEval (L (8*r)) (L j) (L (j+1)) ≤ 0) := by
    rw [oriented_nonneg_iff _ _ _ hdA,oriented_nonpos_iff _ _ _ hdA]
    rw [hzero]
    simp only [affineEval,graphLine,zero_mul,neg_mul,one_mul,sub_zero,zero_add]
    exact ⟨fun he => by have h := hapex.1 he; linarith,
      fun ho => by have h := hapex.2 ho; linarith⟩
  have hends (s : Fin (8*r+1)) (hsq : 4*r ≤ s.val) :
      (j%2=0 →
        0 ≤ affineEval (L s) (intersection (L (4*r+i)) (L j)) ∧
        0 ≤ affineEval (L s) (intersection (L (4*r+i)) (L (j+1)))) ∧
      (j%2≠0 →
        affineEval (L s) (intersection (L (4*r+i)) (L j)) ≤ 0 ∧
        affineEval (L s) (intersection (L (4*r+i)) (L (j+1))) ≤ 0) := by
    by_cases hz : s.val=8*r
    · rw [hz]
      have hl := cap_endpoint_height r j j hr hj hc (Or.inl rfl) L w m a hp horder
        hgraph hzero hmneg hmpos hdir
      have hr' := cap_endpoint_height r j (j+1) hr hj hc (Or.inr rfl) L w m a hp horder
        hgraph hzero hmneg hmpos hdir
      exact ⟨fun he => ⟨hl.1 he,hr'.1 he⟩,fun ho => ⟨hl.2 ho,hr'.2 ho⟩⟩
    · let k := s.val-4*r
      have hk : k < 4*r := by dsimp [k]; omega
      have heq : s.val=4*r+k := by dsimp [k]; omega
      rw [heq]
      by_cases hki : k=i
      · rw [hki]
        have hdL' : det (L (4*r+i)) (L j) ≠ 0 := by
          rw [det_skew]; exact neg_ne_zero.mpr hdL
        have hdR' : det (L (4*r+i)) (L (j+1)) ≠ 0 := by
          rw [det_skew]; exact neg_ne_zero.mpr hdR
        rw [intersection_on_left _ _ hdL',intersection_on_left _ _ hdR']
        exact ⟨fun _ => ⟨le_rfl,le_rfl⟩,fun _ => ⟨le_rfl,le_rfl⟩⟩
      · have hl := cap_left_endpoint r j k hr hj hc hk hki L w m a hp hw horder
          hgraph hzero hmneg hmpos ha
        have hr' := cap_right_endpoint r j k hr hj hc hk hki L w m a hp hs hw horder
          hgraph hzero hmneg hmpos ha
        exact ⟨fun he => ⟨hl.1 he,hr'.1 he⟩,fun ho => ⟨hl.2 ho,hr'.2 ho⟩⟩
  intro s hsq
  have he := hends s hsq
  have hl : (j%2=0 → 0 ≤ orientedEval (L s) (L j) (L (4*r+i))) ∧
      (j%2≠0 → orientedEval (L s) (L j) (L (4*r+i)) ≤ 0) := by
    rw [oriented_nonneg_iff _ _ _ hdL,oriented_nonpos_iff _ _ _ hdL,
      intersection_swap (L j) (L (4*r+i))]
    exact ⟨fun h => (he.1 h).1,fun h => (he.2 h).1⟩
  have hr' : (j%2=0 → 0 ≤ orientedEval (L s) (L (j+1)) (L (4*r+i))) ∧
      (j%2≠0 → orientedEval (L s) (L (j+1)) (L (4*r+i)) ≤ 0) := by
    rw [oriented_nonneg_iff _ _ _ hdR,oriented_nonpos_iff _ _ _ hdR,
      intersection_swap (L (j+1)) (L (4*r+i))]
    exact ⟨fun h => (he.1 h).2,fun h => (he.2 h).2⟩
  by_cases heven : j%2=0
  · exact ⟨mul_nonneg (hv.1 heven) (hl.1 heven),mul_nonneg (hv.1 heven) (hr'.1 heven)⟩
  · exact ⟨mul_nonneg_of_nonpos_of_nonpos (hv.2 heven) (hl.2 heven),
      mul_nonneg_of_nonpos_of_nonpos (hv.2 heven) (hr'.2 heven)⟩

#print axioms canonical_endpoint_signs

theorem endpointSigns_of_canonical (r j : Nat) (hr : 1 ≤ r) (hj : j < 4*r-1)
    (hc : j ≠ 2*r-1) (old D : Nat → Line ℝ) (κ : ℝ)
    (he : CanonicalEndpointSigns r j
      (Reindex.rotate (8*r+1) (pencilAppend (4*r+1) old D 0 κ))) :
    EndpointSigns (4*r+1) (4*r) (capRow r j) (j+1) (j+2) old D κ := by
  let raw := pencilAppend (4*r+1) old D 0 κ
  let L := Reindex.rotate (8*r+1) raw
  have hcap : capRow r j < 4*r := capRow_ne_horizontal r j hr hj hc
  have hrot (t : Nat) (ht : t+1 < 8*r+1) : L t=raw (t+1) := by
    simp [L,Reindex.rotate,Reindex.shift,ht]
  have hlast : L (8*r)=old 0 := by
    simp [L,raw,Reindex.rotate,Reindex.shift,pencilAppend]
  have hlo : L j=old (j+1) := by
    rw [hrot j (by omega)]
    simp [raw,pencilAppend,show j+1 < 4*r+1 by omega]
  have hhi : L (j+1)=old (j+2) := by
    rw [hrot (j+1) (by omega)]
    simp [raw,pencilAppend,show j+1+1 < 4*r+1 by omega,Nat.add_assoc]
  have hM : L (4*r+capRow r j)=perturb (old 0) (D (capRow r j)) κ := by
    rw [hrot (4*r+capRow r j) (by omega)]
    have hind : 4*r+capRow r j+1=(4*r+1)+capRow r j := by omega
    rw [hind]
    simp [raw,pencilAppend,show ¬(4*r+1+capRow r j < 4*r+1) by omega]
  change CanonicalEndpointSigns r j L at he
  intro s hs
  change 0 ≤ orientedEval (old 0) (old (j+1)) (old (j+2))*
      orientedEval (raw s) (old (j+1)) (perturb (old 0) (D (capRow r j)) κ) ∧
    0 ≤ orientedEval (old 0) (old (j+1)) (old (j+2))*
      orientedEval (raw s) (old (j+2)) (perturb (old 0) (D (capRow r j)) κ)
  rcases hs with hs0 | hsn
  · have hraw : raw s=old 0 := by simp [raw,pencilAppend,hs0]
    have hh := he ⟨8*r,by omega⟩ (show 4*r ≤ 8*r by omega)
    dsimp only at hh
    simpa only [hlast,hlo,hhi,hM,hraw] using hh
  · have hsp : 1 ≤ s.val := by omega
    have hsu : s.val-1 < 8*r+1 := by omega
    have hcu : L (s.val-1)=raw s := by
      rw [hrot (s.val-1) (by omega),Nat.sub_add_cancel hsp]
    have hh := he ⟨s.val-1,hsu⟩ (show 4*r ≤ s.val-1 by omega)
    dsimp only at hh
    simpa only [hlast,hlo,hhi,hM,hcu] using hh

#print axioms endpointSigns_of_canonical

open Filter
open scoped Topology

theorem cap_replaced_eventually (r j : Nat) (hr : 1 ≤ r) (hj : j < 4*r-1)
    (hc : j ≠ 2*r-1) (old D : Nat → Line ℝ)
    (hp : NoParallel (4*r+1) old) (hs : NoConcurrent (4*r+1) old)
    (ht : TrianglePredicate (4*r+1) old ⟨0,j+1,j+2⟩) :
    ∀ᶠ κ in 𝓝 (0:ℝ),
      CanonicalEndpointSigns r j
        (Reindex.rotate (8*r+1) (pencilAppend (4*r+1) old D 0 κ)) →
      TrianglePredicate (8*r+1)
        (Reindex.rotate (8*r+1) (pencilAppend (4*r+1) old D 0 κ))
        ⟨j,j+1,4*r+capRow r j⟩ := by
  have hcap := capRow_ne_horizontal r j hr hj hc
  have hh := cap_replacement_eventually (4*r+1) (4*r) (capRow r j) (j+1) (j+2)
    old D hp hs ht hcap
  apply hh.mono
  intro κ hκ he
  have hraw := hκ (endpointSigns_of_canonical r j hr hj hc old D κ he)
  have hN : 4*r+1+4*r=8*r+1 := by omega
  rw [hN] at hraw
  have hrot := Reindex.rotate_triangle (8*r+1) (pencilAppend (4*r+1) old D 0 κ)
    ⟨j+1,j+2,4*r+1+capRow r j⟩ hraw (show 0 < j+1 by omega)
  have hidx : 4*r+1+capRow r j-1=4*r+capRow r j := by omega
  simpa only [Nat.add_sub_cancel_right,show j+2-1=j+1 by omega,hidx] using hrot

#print axioms cap_replaced_eventually
end Kobon.BBLCapBridge
