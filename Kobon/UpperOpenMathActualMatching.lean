import Kobon.UpperOpenMathActualFans
import Kobon.UpperOpenMathFiberMatching

/-!
# Actual matching of adjacent core fans

For an actual shared core-to-core side, its reverse endpoint has a canonical
ray in the neighboring core chart. Its neighboring sector endpoints match
the same two original certified triangles. The equations used by the local
triple-fan obstruction are therefore derived, rather than supplied.
-/
namespace Kobon.UpperOpenMathActualMatching
open Cells FanGeometry UpperVertexBudget UpperTriangleIncidence UpperSharedIncidence
  UpperCoreExtraction UpperOpenMathRadialOrder UpperOpenMathActualFans
  UpperOpenMathSectorRecords Finset

theorem core_vertex (n : ℕ) (L : ℕ → Line ℝ) {c : Point} (hc : c∈core n L) :
    c∈vertices n L := by
  classical
  exact (mem_filter.mp hc).1

theorem certificate_neighbor_matching {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (c d : Point) (hc : c∈core n L) (hd : d∈core n L)
    (D : OrderedDirections n L (supports n L c))
    (E : OrderedDirections n L (supports n L d))
    [NeZero (2*(supports n L c).card)] [NeZero (2*(supports n L d).card)]
    (hrc : 2≤(supports n L c).card) (hrd : 2≤(supports n L d).card)
    (z : ZMod (2*(supports n L c).card))
    (shared : z∈(fan n L hL hn tri ht c (core_vertex n L hc) D hrc).coreShared)
    (neighbor : d=(fan n L hL hn tri ht c (core_vertex n L hc) D hrc).point z) :
    ∃ w : ZMod (2*(supports n L d).card),
      w∈(fan n L hL hn tri ht d (core_vertex n L hd) E hrd).coreShared ∧
      (fan n L hL hn tri ht d (core_vertex n L hd) E hrd).point w=c ∧
      (fan n L hL hn tri ht d (core_vertex n L hd) E hrd).point (w-1)=
        (fan n L hL hn tri ht c (core_vertex n L hc) D hrc).point (z+1) ∧
      (fan n L hL hn tri ht d (core_vertex n L hd) E hrd).point (w+1)=
        (fan n L hL hn tri ht c (core_vertex n L hc) D hrc).point (z-1) := by
  classical
  let G := fun a => ofPredicate n L (tri a) hL (ht a)
  let f := fan n L hL hn tri ht c (mem_filter.mp hc).1 D hrc
  let g := fan n L hL hn tri ht d (mem_filter.mp hd).1 E hrd
  have he := (fan_core_iff n L hL hn tri ht c (mem_filter.mp hc).1 D hrc hi hc z).mp shared
  have hused := (mem_filter.mp (mem_sdiff.mp he).1).1
  have hpneq : f.point z≠c := fan_point_ne_center n L hL hn tri ht c (mem_filter.mp hc).1 D hrc z
  have hcd : c≠d := by intro h; exact hpneq (neighbor.symm.trans h.symm)
  have hpair : {d,c}∈usedEdges G := by
    simpa only [← neighbor,pair_comm] using hused
  obtain ⟨w,hw⟩ := used_edge_has_ray n L hL hn tri ht d (mem_filter.mp hd).1 E c hcd hpair
  change g.point w=c at hw
  have hew : {d,g.point w}∈twoCoreEdges n L G := by
    rw [hw,neighbor,pair_comm]
    exact he
  have hgw := (fan_core_iff n L hL hn tri ht d (mem_filter.mp hd).1 E hrd hi hd w).mpr hew
  have hfs := (mem_sdiff.mp shared).1
  have hgs := (mem_sdiff.mp hgw).1
  have hftri : z∈triangular G c f.point := (mem_filter.mp hfs).1
  have hfprev : z-1∈triangular G c f.point := (mem_filter.mp hfs).2
  have hgtri : w∈triangular G d g.point := (mem_filter.mp hgs).1
  have hgprev : w-1∈triangular G d g.point := (mem_filter.mp hgs).2
  obtain ⟨o⟩ := (mem_triangular G c f.point (z-1)).mp hfprev
  obtain ⟨p⟩ := (mem_triangular G c f.point z).mp hftri
  obtain ⟨a⟩ := (mem_triangular G d g.point (w-1)).mp hgprev
  obtain ⟨b⟩ := (mem_triangular G d g.point w).mp hgtri
  have disjoint : Pairwise (fun a b => Disjoint (G a).interior (G b).interior) := by
    intro a b hab
    exact distinct_interiors_disjoint n L _ _ hL (ht a) (ht b) (fun h => hab (hi h))
  have matching := UpperOpenMathFiberMatching.neighboring_points_match G disjoint
    hrc hrd c d f.point g.point
    (fan_point_injective n L hL hn tri ht c (mem_filter.mp hc).1 D hrc)
    (fan_point_injective n L hL hn tri ht d (mem_filter.mp hd).1 E hrd)
    (fan_point_ne_center n L hL hn tri ht c (mem_filter.mp hc).1 D hrc)
    (fan_point_ne_center n L hL hn tri ht d (mem_filter.mp hd).1 E hrd)
    (fan_positive n L hL hn tri ht c (mem_filter.mp hc).1 D hrc)
    (fan_positive n L hL hn tri ht d (mem_filter.mp hd).1 E hrd)
    z w neighbor hw o p a b
  exact ⟨w,hgw,hw,matching⟩

#print axioms certificate_neighbor_matching
end Kobon.UpperOpenMathActualMatching
