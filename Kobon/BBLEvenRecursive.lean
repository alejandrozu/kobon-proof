import Kobon.BBLEvenStep

/-! Closure of the actual triangle-and-visible-boundary invariant. -/
namespace Kobon.BBLEvenRecursive
open Real Exterior BBLExtrema BBLAnalytic BBLGridReindex BBLNextSaturation
  BBLCrossingCoordinates BBLRealization BBLRealizedPencil BBLCanonicalPencil
  BBLRecursiveGrid BBLRecursiveSeed BBLVisibleSeed BBLNextBoundary BBLEvenStep

theorem visible_seed_step (r T V : Nat) (hr : 5≤r) (ε : ℝ)
    (hε0 : 0<ε) (hε : ε<tan (alpha r/2)) (w : Line ℝ) (hwa : 0<w.a)
    (s : VisibleSeed r T V ε w) :
    Nonempty (VisibleSeed (2*r) (T+(4*r)^2) (V+2*r) ε w) := by
  obtain ⟨δ,κ,hδ,hκ,hp,hs,ho,hcp,hsat,hw,hpos,ts,vs,hn,hvn,ht,hv,hcount,hvcount⟩ :=
    canonical_visible_step r T V hr ε hε0 hε w hwa s
  let L := arrangement r ε s.slopes δ κ
  let m := nextSlopes r s.slopes δ κ
  let M := oldArrangement (2*r) ε m
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
  obtain ⟨uvs,huvn,huvv,huvc⟩ := BBLVisibleReindex.transport_list (8*r+1) L w f (backward r)
    hf (backward_bound r) (forward_backward r) vs hvn hv
  have hsaturated : ∀ j, j<8*r-1 → TrianglePredicate (8*r+1) M ⟨0,j+1,j+2⟩ := by
    intro j hj
    apply BBLRecursiveSeed.triangle_congr (8*r+1) (fun i => L (f i)) M heq
    exact Permutation.triangle_pullback_support (8*r+1) (8*r+1) L f hf
      (gapTriangle r j) (hsat j hj) 0 (j+1) (j+2)
      (by omega) (by omega) (by omega) (gap_support r j)
  have hcpos : 0 < (intersection (M (4*r)) (M (4*r+1))).2 := by
    rw [← heq (4*r) (by omega),← heq (4*r+1) (by omega)]
    simpa only [f,forward_central_left r (by omega),forward_central_right r (by omega)] using hcp
  have hsize : 4*(2*r)+1=8*r+1 := by omega
  have hmid : 2*(2*r)=4*r := by omega
  have hm_last : m (8*r-1)=κ*BBLIntersection.slopeFactor δ (newIntercept r (4*r-1)) := by
    dsimp [m,nextSlopes]
    rw [rightmost r (by omega),if_neg (by omega)]
    rw [show 8*r-1-4*r=4*r-1 by omega]
  have hf_last : f (8*r)=8*r-1 := by
    dsimp [f,forward]
    rw [if_neg (by omega),rightmost r (by omega)]
  have hIntercept : oldIntercept (2*r) ε (8*r-1)=newIntercept r (4*r-1) := by
    rw [old_intercept_perm r hr ε (8*r-1) (by omega),rightmost r (by omega),if_neg (by omega)]
    congr 1
    omega
  have hbdy : ∀ i : Fin (8*r+1), i.val≠8*r →
      (intersection (M (8*r)) (M i)).1≤oldIntercept (2*r) ε (8*r-1) := by
    intro i hi
    rw [← heq (8*r) (by omega),← heq i i.isLt]
    change (intersection (L (f (8*r))) (L (f i))).1≤oldIntercept (2*r) ε (8*r-1)
    rw [hf_last,hIntercept]
    have hfi : f i≠8*r-1 := by
      intro he
      have hi' := forward_injective r i ⟨8*r,by omega⟩ (by simpa only [← hf_last] using he)
      exact hi (congrArg Fin.val hi')
    exact next_rightmost_boundary r hr ε s.slopes δ κ hδ hκ hp hs ho ⟨f i,hf i⟩ hfi
  let base : Seed (2*r) (T+(4*r)^2) ε := {
    slopes := m
    triangles := us
    no_parallel := by rw [hsize]; exact BBLRecursiveSeed.no_parallel_congr _ _ M heq hp'
    no_concurrent := by rw [hsize]; exact BBLRecursiveSeed.no_concurrent_congr _ _ M heq hs'
    saturated := by simpa only [show 4*(2*r)=8*r by omega] using hsaturated
    central_positive := by simpa only [hmid] using hcpos
    nodup := hun
    valid := by
      intro t htu
      rw [hsize]
      exact BBLRecursiveSeed.triangle_congr _ _ M heq t (hut t htu)
    count := by omega }
  refine ⟨{
    toSeed := base
    visible := uvs
    visible_nodup := huvn
    visible_valid := ?_
    visible_count := by omega
    admissible := ?_
    right_positive := ?_
    right_direction := ?_
    right_boundary := ?_ }⟩
  · intro t htuv
    change VisiblePair (4*(2*r)+1) M w t
    rw [hsize]
    exact BBLVisibleReindex.visible_congr _ _ M w heq t (huvv t htuv)
  · change Admissible (4*(2*r)+1) M w
    rw [hsize]
    exact BBLVisibleReindex.admissible_congr _ _ M w heq
      (BBLVisibleReindex.admissible_pullback _ _ L w f hf hw)
  · change 0<m (4*(2*r)-1)
    rw [show 4*(2*r)=8*r by omega,hm_last]
    exact new_slopes_pos r hr δ κ hδ hκ (4*r-1) (by omega) (by omega)
  · change 0<w.a+w.b*m (4*(2*r)-1)
    rw [show 4*(2*r)=8*r by omega,hm_last]
    simpa only [auxSlope,if_pos (show 4*r-1<4*r by omega)] using hpos (4*r-1) (by omega)
  · change ∀ i : Fin (4*(2*r)+1), i.val≠4*(2*r) →
      (intersection (M (4*(2*r))) (M i)).1≤oldIntercept (2*r) ε (4*(2*r)-1)
    intro i hi
    have hh := hbdy ⟨i.val,by have := i.isLt; omega⟩ (by change i.val≠8*r; omega)
    simpa only [show 4*(2*r)=8*r by omega] using hh

#print axioms visible_seed_step
end Kobon.BBLEvenRecursive
