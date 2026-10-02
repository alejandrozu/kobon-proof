import Kobon.BBLRecursiveWitness
import Kobon.BBLRecursiveGrid
import Kobon.Permutation

/-! The recursive geometric invariant, retaining actual real straight lines.
The small parameter is fixed for one step, not for all iteration depths. -/
namespace Kobon.BBLRecursiveSeed
open Real Exterior BBLExtrema BBLAnalytic BBLGridReindex BBLNextSaturation
  BBLCrossingCoordinates BBLRealizedPencil BBLRecursiveGrid BBLRecursiveWitness

structure Seed (r T : Nat) (ε : ℝ) where
  slopes : Nat→ℝ
  triangles : List Triple
  no_parallel : NoParallel (4*r+1) (oldArrangement r ε slopes)
  no_concurrent : NoConcurrent (4*r+1) (oldArrangement r ε slopes)
  saturated : ∀ j, j<4*r-1 →
    TrianglePredicate (4*r+1) (oldArrangement r ε slopes) ⟨0,j+1,j+2⟩
  central_positive : 0 < (intersection (oldArrangement r ε slopes (2*r))
    (oldArrangement r ε slopes (2*r+1))).2
  nodup : triangles.Nodup
  valid : ∀ t∈triangles, TrianglePredicate (4*r+1) (oldArrangement r ε slopes) t
  count : T≤triangles.length

def Compatible (r T : Nat) (ε : ℝ) : Prop := Nonempty (Seed r T ε)

theorem triangle_congr (n : Nat) (L M : Nat→Line ℝ)
    (heq : ∀ i, i<n → L i=M i) (t : Triple) (ht : TrianglePredicate n L t) :
    TrianglePredicate n M t := by
  have hi : t.i<n := by have := ht.1; have := ht.2.1; have := ht.2.2.1; omega
  have hj : t.j<n := by have := ht.2.1; have := ht.2.2.1; omega
  have hk := ht.2.2.1
  refine ⟨ht.1,ht.2.1,hk,?_,?_⟩
  · simpa only [heq t.i hi,heq t.j hj,heq t.k hk] using ht.2.2.2.1
  · intro i
    simpa only [heq i i.isLt,heq t.i hi,heq t.j hj,heq t.k hk] using ht.2.2.2.2 i

theorem no_parallel_congr (n : Nat) (L M : Nat→Line ℝ)
    (heq : ∀ i, i<n → L i=M i) (hp : NoParallel n L) : NoParallel n M := by
  intro i j hij
  simpa only [heq i i.isLt,heq j j.isLt] using hp i j hij

theorem no_concurrent_congr (n : Nat) (L M : Nat→Line ℝ)
    (heq : ∀ i, i<n → L i=M i) (hs : NoConcurrent n L) : NoConcurrent n M := by
  intro i j k hij hjk
  simpa only [heq i i.isLt,heq j j.isLt,heq k k.isLt] using hs i j k hij hjk

theorem gap_support (r j : Nat) (x : Nat) :
    (x=forward r 0 ∨ x=forward r (j+1) ∨ x=forward r (j+2)) ↔
      (x=(gapTriangle r j).i ∨ x=(gapTriangle r j).j ∨ x=(gapTriangle r j).k) := by
  simp only [forward,if_pos rfl,Nat.add_eq_zero_iff,one_ne_zero,and_false,
    Nat.succ_ne_zero,if_false,Nat.add_sub_cancel,gapTriangle]
  have hh : j+2-1=j+1 := by omega
  simp only [hh]
  rcases le_total (perm r j) (perm r (j+1)) with h | h
  · rw [min_eq_left h,max_eq_right h]
    tauto
  · rw [min_eq_right h,max_eq_left h]
    tauto

/-- The saturated geometric invariant is closed under actual BBL doubling. -/
theorem seed_step (r T : Nat) (hr : 5≤r) (ε : ℝ)
    (hε0 : 0<ε) (hε : ε<tan (alpha r/2)) (s : Seed r T ε) :
    Nonempty (Seed (2*r) (T+(4*r)^2) ε) := by
  obtain ⟨δ,κ,hδ,hκ,hp,hs,ho,hct,hcp,hsat,ts,hn,ht,hcount⟩ :=
    canonical_step r T hr ε hε0 hε s.slopes s.no_parallel s.no_concurrent
      s.saturated s.central_positive s.triangles s.nodup s.valid s.count
  let L := arrangement r ε s.slopes δ κ
  let M := oldArrangement (2*r) ε (nextSlopes r s.slopes δ κ)
  let f := forward r
  have hf : ∀ i : Fin (8*r+1), f i<8*r+1 := fun i => forward_bound r i i.isLt
  have heq : ∀ i, i<8*r+1 → (fun k => L (f k)) i=M i := by
    intro i hi
    exact (graph_reindex r hr ε s.slopes δ κ i hi).symm
  have hp' := Reindex.no_parallel_pullback (8*r+1) (8*r+1) L f hf
    (forward_injective r) hp
  have hs' := Reindex.no_concurrent_pullback (8*r+1) (8*r+1) L f hf
    (forward_injective r) hs
  obtain ⟨us,hun,hut,huc⟩ := Permutation.transport_list (8*r+1) L f (backward r)
    hf (backward_bound r) (forward_backward r) ts hn ht
  have hsaturated : ∀ j, j<8*r-1 → TrianglePredicate (8*r+1) M ⟨0,j+1,j+2⟩ := by
    intro j hj
    apply triangle_congr (8*r+1) (fun i => L (f i)) M heq
    exact Permutation.triangle_pullback_support (8*r+1) (8*r+1) L f hf
      (gapTriangle r j) (hsat j hj) 0 (j+1) (j+2)
      (by omega) (by omega) (by omega) (gap_support r j)
  have hcpos : 0 < (intersection (M (4*r)) (M (4*r+1))).2 := by
    rw [← heq (4*r) (by omega),← heq (4*r+1) (by omega)]
    simpa only [f,forward_central_left r (by omega),forward_central_right r (by omega)]
      using hcp
  have hsize : 4*(2*r)+1=8*r+1 := by omega
  have hmid : 2*(2*r)=4*r := by omega
  refine ⟨⟨nextSlopes r s.slopes δ κ,us,?_,?_,?_,?_,hun,?_,?_⟩⟩
  · rw [hsize]
    exact no_parallel_congr (8*r+1) _ M heq hp'
  · rw [hsize]
    exact no_concurrent_congr (8*r+1) _ M heq hs'
  · simpa only [show 4*(2*r)=8*r by omega] using hsaturated
  · simpa only [hmid] using hcpos
  · intro t htu
    rw [hsize]
    exact triangle_congr (8*r+1) _ M heq t (hut t htu)
  · omega

theorem compatible_step (r T : Nat) (hr : 5≤r) (ε : ℝ)
    (hε0 : 0<ε) (hε : ε<tan (alpha r/2)) (h : Compatible r T ε) :
    Compatible (2*r) (T+(4*r)^2) ε := by
  obtain ⟨s⟩ := h
  exact seed_step r T hr ε hε0 hε s

theorem seed_lower_bound (r T : Nat) (ε : ℝ) (h : Compatible r T ε) :
    SimpleLowerBound (4*r+1) T := by
  obtain ⟨s⟩ := h
  exact ⟨oldArrangement r ε s.slopes,s.no_parallel,s.no_concurrent,s.triangles,
    s.nodup,s.valid,s.count⟩

#print axioms seed_step
end Kobon.BBLRecursiveSeed
