import Kobon.BBLCapEnvelope

/-! A triangular cell supported by Y0 uses consecutive Y0 intersections. -/
namespace Kobon.BBLConsecutive
open Exterior HybridBoundary BBLExtrema BBLCapEnvelope

theorem supports_consecutive (q i j : Nat) (L : Nat → Line ℝ) (m a : Nat → ℝ)
    (hp : NoParallel (q+1) L) (hzero : L 0=graphLine 0 0)
    (hgraph : ∀ t < q, L (t+1)=graphLine (m t) (a t))
    (hordered : ∀ s t, s < t → t < q → a s < a t)
    (ht : TrianglePredicate (q+1) L ⟨0,i,j⟩) : j=i+1 := by
  obtain ⟨hi,hij,hj,hn,hempty⟩ := ht
  dsimp at hi hij hj hn hempty
  have hmi : m (i-1) ≠ 0 := by
    have hd := hp ⟨0,by omega⟩ ⟨i,by omega⟩ hi
    have hg : L i=graphLine (m (i-1)) (a (i-1)) := by
      have h := hgraph (i-1) (by omega)
      simpa [Nat.sub_add_cancel (show 1 ≤ i by omega)] using h
    simpa [hzero,hg,det,graphLine] using hd
  have hmj : m (j-1) ≠ 0 := by
    have hd := hp ⟨0,by omega⟩ ⟨j,by omega⟩ (show (0:Nat) < j by omega)
    have hg : L j=graphLine (m (j-1)) (a (j-1)) := by
      have h := hgraph (j-1) (by omega)
      simpa [Nat.sub_add_cancel (show 1 ≤ j by omega)] using h
    simpa [hzero,hg,det,graphLine] using hd
  have hgi : L i=graphLine (m (i-1)) (a (i-1)) := by
    have h := hgraph (i-1) (by omega)
    simpa [Nat.sub_add_cancel (show 1 ≤ i by omega)] using h
  have hgj : L j=graphLine (m (j-1)) (a (j-1)) := by
    have h := hgraph (j-1) (by omega)
    simpa [Nat.sub_add_cancel (show 1 ≤ j by omega)] using h
  have hPi : intersection (L 0) (L i)=(a (i-1),0) := by
    rw [intersection_swap,hgi,hzero,graph_horizontal_intersection _ _ hmi]
  have hPj : intersection (L 0) (L j)=(a (j-1),0) := by
    rw [intersection_swap,hgj,hzero,graph_horizontal_intersection _ _ hmj]
  by_contra he
  have hgap : i+1 < j := by omega
  have hik : a (i-1) < a i := hordered (i-1) i (by omega) (by omega)
  have hkj : a i < a (j-1) := hordered i (j-1) (by omega) (by omega)
  have hmk : m i ≠ 0 := by
    have hd := hp ⟨0,by omega⟩ ⟨i+1,by omega⟩ (show (0:Nat) < i+1 by omega)
    simpa [hzero,hgraph i (by omega),det,graphLine] using hd
  have hp0i := hp ⟨0,by omega⟩ ⟨i,by omega⟩ hi
  have hp0j := hp ⟨0,by omega⟩ ⟨j,by omega⟩ (show (0:Nat) < j by omega)
  have htst := hempty ⟨i+1,by omega⟩
  rw [oriented_nonneg_iff _ _ _ hp0i,oriented_nonneg_iff _ _ _ hp0j,
      oriented_nonpos_iff _ _ _ hp0i,oriented_nonpos_iff _ _ _ hp0j,
      hPi,hPj,hgraph i (by omega)] at htst
  simp only [affineEval,graphLine,mul_zero,add_zero] at htst
  rcases lt_or_gt_of_ne hmk with hm | hm
  · have hl : 0 < m i*(a (i-1)-a i) := mul_pos_of_neg_of_neg hm (by linarith)
    have hr : m i*(a (j-1)-a i) < 0 := mul_neg_of_neg_of_pos hm (by linarith)
    rcases htst with ⟨h1,h2,h3⟩ | ⟨h1,h2,h3⟩ <;> nlinarith only [hl,hr,h1,h2]
  · have hl : m i*(a (i-1)-a i) < 0 := mul_neg_of_pos_of_neg hm (by linarith)
    have hr : 0 < m i*(a (j-1)-a i) := mul_pos hm (by linarith)
    rcases htst with ⟨h1,h2,h3⟩ | ⟨h1,h2,h3⟩ <;> nlinarith only [hl,hr,h1,h2]

#print axioms supports_consecutive
end Kobon.BBLConsecutive
