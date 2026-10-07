import Kobon.UpperOpenMathFullCoreFans

/-! Normalized two-cap charts require only high total neighbor sharing;
ordinary sharing degree two at every neighbor is unnecessary. -/
namespace Kobon.UpperOpenMathHighNeighborCharts
open Cells FanGeometry UpperFan UpperVertexBudget UpperTriangleIncidence
  UpperSharedIncidence UpperCoreExtraction UpperOpenMathRadialOrder
  UpperOpenMathActualFans UpperOpenMathCapHeavyTriples UpperOpenMathTripleCharts Finset
set_option maxHeartbeats 1000000

theorem certificate_high_neighbor_normalized_chart {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (c : Point) (hc : c∈core n L) (rc : (supports n L c).card=3)
    (ordc : ordinaryDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) c=2)
    (corc : coreDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) c=2)
    (neighbors : ∀ d∈core n L,
      {c,d}∈twoCoreEdges n L (fun a => ofPredicate n L (tri a) hL (ht a)) →
      (supports n L d).card=3 ∧ 3≤ordinaryDegree n L
        (fun a => ofPredicate n L (tri a) hL (ht a)) d+coreDegree n L
        (fun a => ofPredicate n L (tri a) hL (ht a)) d) :
    ∃ f : UpperFan.Sectors n 3 L, f.center=c ∧
      NormalizedData (fun a => ofPredicate n L (tri a) hL (ht a)) f := by
  classical
  let G := fun a => ofPredicate n L (tri a) hL (ht a)
  letI : NeZero (2*(supports n L c).card) := ⟨by omega⟩
  let D := atPoint n L hL hn c
  let f := fan n L hL hn tri ht c (mem_filter.mp hc).1 D (by omega)
  have ord : f.ordinaryShared.card=2 := by
    rw [fan_ordinary_card n L hL hn tri ht c (mem_filter.mp hc).1 D (by omega) hi hc]
    exact ordc
  have cor : f.coreShared.card=2 := by
    rw [fan_core_card n L hL hn tri ht c (mem_filter.mp hc).1 D (by omega) hi hc]
    exact corc
  have ce : ∀ z∈f.coreShared, f.point z∈core n L :=
    fan_core_endpoint n L hL hn tri ht c (mem_filter.mp hc).1 D (by omega) hi hc
  have im : f.coreShared.image (fun z => ({f.center,f.point z} : Edge))=
      (twoCoreEdges n L G).filter (fun e => f.center∈e) :=
    fan_core_image n L hL hn tri ht c (mem_filter.mp hc).1 D (by omega) hi hc
  have occ : ∀ z∈f.triangular, Nonempty
      (UpperOpenMathSectorRecords.Occurrence G f.center f.point z) := by
    intro z hz
    exact (UpperOpenMathSectorRecords.mem_triangular G c f.point z).mp hz
  have nm : ∀ z∈f.coreShared, ¬(z-1∈f.ordinaryShared ∧ z+1∈f.ordinaryShared) := by
    intro z hz marked
    let d := f.point z
    have hd := ce z hz
    have he := (fan_core_iff n L hL hn tri ht c (mem_filter.mp hc).1 D (by omega) hi hc z).mp hz
    obtain ⟨rd,total⟩ := neighbors d hd he
    letI : NeZero (2*(supports n L d).card) := ⟨by omega⟩
    let E := atPoint n L hL hn d
    let g := fan n L hL hn tri ht d (mem_filter.mp hd).1 E (by omega)
    obtain ⟨w,gcore,gw,right,left⟩ := UpperOpenMathActualMatching.certificate_neighbor_matching
      n L hL hn tri hi ht c d hc hd D E (by omega) (by omega) z hz rfl
    have poor := UpperOpenMathMarkedPoverty.marked_neighbor_poverty_sum_card
      rc rd hL f g z w marked.1 marked.2 gcore rfl gw right left
      (fan_positive n L hL hn tri ht c (mem_filter.mp hc).1 D (by omega))
    rw [fan_ordinary_card n L hL hn tri ht d (mem_filter.mp hd).1 E (by omega) hi hd,
      fan_core_card n L hL hn tri ht d (mem_filter.mp hd).1 E (by omega) hi hd] at poor
    have poorSum : ordinaryDegree n L G d+coreDegree n L G d≤2 := poor.2
    change 3≤ordinaryDegree n L G d+coreDegree n L G d at total
    omega
  obtain ⟨g,hg,dg⟩ := lift_three G rc f
    (fan_point_injective n L hL hn tri ht c (mem_filter.mp hc).1 D (by omega))
    (fan_point_ne_center n L hL hn tri ht c (mem_filter.mp hc).1 D (by omega))
    (fan_positive n L hL hn tri ht c (mem_filter.mp hc).1 D (by omega))
    ord cor ce im occ nm
  obtain ⟨h,hh,dh⟩ := normalized_exists G g dg
  exact ⟨h,hh.trans hg,dh⟩


#print axioms certificate_high_neighbor_normalized_chart
end Kobon.UpperOpenMathHighNeighborCharts
