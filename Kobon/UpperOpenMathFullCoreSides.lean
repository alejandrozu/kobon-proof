import Kobon.UpperOpenMathFullSharing

/-! Every actual selected side from a full core to another core is shared.
This is extracted from canonical rays, rather than assumed as a graph rule. -/
namespace Kobon.UpperOpenMathFullCoreSides
open Cells FanGeometry UpperFan UpperVertexBudget UpperTriangleIncidence
  UpperSharedIncidence UpperCoreExtraction UpperOpenMathRadialOrder
  UpperOpenMathSectorRecords UpperOpenMathActualFans UpperOpenMathCapHeavyTriples Finset
set_option maxHeartbeats 1000000

theorem certificate_full_core_side_shared {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (c q : Point) (hc : c∈core n L) (hq : q∈core n L)
    (side : {c,q}∈usedEdges (fun a => ofPredicate n L (tri a) hL (ht a)))
    (full : ordinaryDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) c+
      coreDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) c=
        2*(supports n L c).card) :
    {c,q}∈twoCoreEdges n L (fun a => ofPredicate n L (tri a) hL (ht a)) := by
  classical
  let G := fun a => ofPredicate n L (tri a) hL (ht a)
  have hr := core_multiplicity n L hL hc
  have qr := core_multiplicity n L hL hq
  have neq : q≠c := by
    intro he
    have hcard := used_edge_card G side
    simp [he] at hcard
  letI : NeZero (2*(supports n L c).card) := ⟨by omega⟩
  let D := atPoint n L hL hn c
  let f := fan n L hL hn tri ht c (mem_filter.mp hc).1 D (by omega)
  obtain ⟨z,hz⟩ := used_edge_has_ray n L hL hn tri ht c (mem_filter.mp hc).1 D q neq side
  change f.point z=q at hz
  have hs : f.shared.card=2*(supports n L c).card := by
    rw [← f.shared_card_split,
      fan_ordinary_card n L hL hn tri ht c (mem_filter.mp hc).1 D (by omega) hi hc,
      fan_core_card n L hL hn tri ht c (mem_filter.mp hc).1 D (by omega) hi hc]
    exact full
  have hall := UpperOpenMathFullSharing.shared_full f hs
  have hzC : z∈f.coreShared := by
    apply mem_sdiff.mpr
    refine ⟨by simp [Sectors.shared,hall],?_⟩
    intro ho
    have ord := ((f.mem_ordinaryShared z).mp ho).2.2
    rw [hz] at ord
    have qo := (ordinary_iff_support_card n L q).mp ord
    omega
  have h := (fan_core_iff n L hL hn tri ht c (mem_filter.mp hc).1 D (by omega) hi hc z).mp hzC
  change ({c,f.point z} : Edge)∈twoCoreEdges n L G at h
  rw [hz] at h
  exact h

#print axioms certificate_full_core_side_shared
end Kobon.UpperOpenMathFullCoreSides
