import Kobon.UpperOpenMathActualMatching

/-!
# Matching at every shared elementary side

The actual fan matching equations also hold when one or both endpoints are
ordinary. This is the interface needed to follow a core cap through a
two-, three-, or four-triangle fan at its ordinary endpoint.
-/
namespace Kobon.UpperOpenMathSharedMatching
open Cells FanGeometry UpperVertexBudget UpperTriangleIncidence UpperSharedIncidence
  UpperCoreExtraction UpperOpenMathRadialOrder UpperOpenMathActualFans
  UpperOpenMathSectorRecords Finset

theorem certificate_shared_neighbor_matching {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (c d : Point) (hc : c∈vertices n L) (hd : d∈vertices n L)
    (D : OrderedDirections n L (supports n L c))
    (E : OrderedDirections n L (supports n L d))
    [NeZero (2*(supports n L c).card)] [NeZero (2*(supports n L d).card)]
    (hrc : 2≤(supports n L c).card) (hrd : 2≤(supports n L d).card)
    (z : ZMod (2*(supports n L c).card))
    (shared : z∈(fan n L hL hn tri ht c hc D hrc).shared)
    (neighbor : d=(fan n L hL hn tri ht c hc D hrc).point z) :
    ∃ w : ZMod (2*(supports n L d).card),
      w∈(fan n L hL hn tri ht d hd E hrd).shared ∧
      (fan n L hL hn tri ht d hd E hrd).point w=c ∧
      (fan n L hL hn tri ht d hd E hrd).point (w-1)=
        (fan n L hL hn tri ht c hc D hrc).point (z+1) ∧
      (fan n L hL hn tri ht d hd E hrd).point (w+1)=
        (fan n L hL hn tri ht c hc D hrc).point (z-1) := by
  classical
  let G := fun a => ofPredicate n L (tri a) hL (ht a)
  let f := fan n L hL hn tri ht c hc D hrc
  let g := fan n L hL hn tri ht d hd E hrd
  have he := (fan_shared_iff n L hL hn tri ht c hc D hrc hi z).mp shared
  have hused := (mem_filter.mp he).1
  have hpneq : f.point z≠c := fan_point_ne_center n L hL hn tri ht c hc D hrc z
  have hcd : c≠d := by intro h; exact hpneq (neighbor.symm.trans h.symm)
  have hpair : {d,c}∈usedEdges G := by
    simpa only [← neighbor,pair_comm] using hused
  obtain ⟨w,hw⟩ := used_edge_has_ray n L hL hn tri ht d hd E c hcd hpair
  change g.point w=c at hw
  have hew : {d,g.point w}∈sharedEdges G := by
    rw [hw,neighbor,pair_comm]
    exact he
  have hgw := (fan_shared_iff n L hL hn tri ht d hd E hrd hi w).mpr hew
  have hftri : z∈triangular G c f.point := (mem_filter.mp shared).1
  have hfprev : z-1∈triangular G c f.point := (mem_filter.mp shared).2
  have hgtri : w∈triangular G d g.point := (mem_filter.mp hgw).1
  have hgprev : w-1∈triangular G d g.point := (mem_filter.mp hgw).2
  obtain ⟨o⟩ := (mem_triangular G c f.point (z-1)).mp hfprev
  obtain ⟨p⟩ := (mem_triangular G c f.point z).mp hftri
  obtain ⟨a⟩ := (mem_triangular G d g.point (w-1)).mp hgprev
  obtain ⟨b⟩ := (mem_triangular G d g.point w).mp hgtri
  have disjoint : Pairwise (fun a b => Disjoint (G a).interior (G b).interior) := by
    intro a b hab
    exact distinct_interiors_disjoint n L _ _ hL (ht a) (ht b) (fun h => hab (hi h))
  have matching := UpperOpenMathFiberMatching.neighboring_points_match G disjoint
    hrc hrd c d f.point g.point
    (fan_point_injective n L hL hn tri ht c hc D hrc)
    (fan_point_injective n L hL hn tri ht d hd E hrd)
    (fan_point_ne_center n L hL hn tri ht c hc D hrc)
    (fan_point_ne_center n L hL hn tri ht d hd E hrd)
    (fan_positive n L hL hn tri ht c hc D hrc)
    (fan_positive n L hL hn tri ht d hd E hrd)
    z w neighbor hw o p a b
  exact ⟨w,hgw,hw,matching⟩

#print axioms certificate_shared_neighbor_matching
end Kobon.UpperOpenMathSharedMatching
