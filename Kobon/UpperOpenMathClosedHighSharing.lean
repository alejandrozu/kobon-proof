import Kobon.UpperOpenMathClosedTwoCapCharts

/-! A closed all-triple subset with sharing degree at least three has no
marked ports. Cores outside this subset may have arbitrary multiplicity. -/
namespace Kobon.UpperOpenMathClosedHighSharing
open Cells FanGeometry UpperFan UpperVertexBudget UpperTriangleIncidence UpperSharedIncidence
  UpperCoreExtraction UpperOpenMathCapHeavyTriples UpperOpenMathCoreComponents
  UpperOpenMathActualFans UpperOpenMathRadialOrder UpperOpenMathMarkedPorts Finset
set_option maxHeartbeats 1000000

theorem certificate_closed_high_zero_marks {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (P : Finset Point) (sub : P⊆core n L)
    (closed : SharedCoreClosed n L (fun a => ofPredicate n L (tri a) hL (ht a)) P)
    (triples : ∀ c∈P, (supports n L c).card=3)
    (high : ∀ c∈P, 3≤ordinaryDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) c+coreDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) c)
    (c : Point) (hc : c∈P) : markedCount n L hL hn tri ht c=0 := by
  classical
  let G := fun a => ofPredicate n L (tri a) hL (ht a)
  have hcC := sub hc
  have rc := triples c hc
  letI : NeZero (2*(supports n L c).card) := ⟨by omega⟩
  let D := atPoint n L hL hn c
  let f := atCoreFan n L hL hn tri ht c hcC
  unfold markedCount
  apply card_eq_zero.mpr
  apply eq_empty_iff_forall_notMem.mpr
  intro e he
  obtain ⟨z,fz,prev,next,ee⟩ := marked_edge_ray n L hL hn tri ht c hcC e he
  let d := f.point z
  have hdC : d∈core n L :=
    fan_core_endpoint n L hL hn tri ht c (mem_filter.mp hcC).1 D (by omega) hi hcC z fz
  have edge : {c,d}∈twoCoreEdges n L G :=
    (fan_core_iff n L hL hn tri ht c (mem_filter.mp hcC).1 D (by omega) hi hcC z).mp fz
  have hd : d∈P := closed {c,d} edge c (by simp) hc (by simp)
  have rd := triples d hd
  letI : NeZero (2*(supports n L d).card) := ⟨by omega⟩
  let E := atPoint n L hL hn d
  let g := fan n L hL hn tri ht d (mem_filter.mp hdC).1 E (by omega)
  obtain ⟨w,gcore,gw,right,left⟩ := UpperOpenMathActualMatching.certificate_neighbor_matching
    n L hL hn tri hi ht c d hcC hdC D E (by omega) (by omega) z fz rfl
  have poor := UpperOpenMathMarkedPoverty.marked_neighbor_poverty_sum_card
    rc rd hL f g z w prev next gcore rfl gw right left
    (fan_positive n L hL hn tri ht c (mem_filter.mp hcC).1 D (by omega))
  rw [fan_ordinary_card n L hL hn tri ht d (mem_filter.mp hdC).1 E (by omega) hi hdC,
    fan_core_card n L hL hn tri ht d (mem_filter.mp hdC).1 E (by omega) hi hdC] at poor
  have hsum := high d hd
  have lowSum : ordinaryDegree n L G d+coreDegree n L G d≤2 := poor.2
  change 3≤ordinaryDegree n L G d+coreDegree n L G d at hsum
  omega

#print axioms certificate_closed_high_zero_marks
end Kobon.UpperOpenMathClosedHighSharing
