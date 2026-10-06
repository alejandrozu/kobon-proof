import Kobon.UpperOpenMathAntipodalTwoCapChart
import Kobon.UpperOpenMathHighNeighborCharts

/-! Actual chart extraction on closed sets whose ordinary sharing degree
is two. Both balanced and full triple fans are normalized without a
global assumption on cores outside the set. -/
namespace Kobon.UpperOpenMathClosedTwoCapCharts
open Cells FanGeometry UpperFan UpperVertexBudget UpperTriangleIncidence UpperSharedIncidence
  UpperCoreExtraction UpperOpenMathCapHeavyTriples UpperOpenMathCoreComponents
  UpperOpenMathActualFans UpperOpenMathRadialOrder UpperOpenMathMarkedPorts Finset
set_option maxHeartbeats 1000000

theorem certificate_closed_two_cap_zero_marks {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (P : Finset Point) (sub : P⊆core n L)
    (closed : SharedCoreClosed n L (fun a => ofPredicate n L (tri a) hL (ht a)) P)
    (triples : ∀ c∈P, (supports n L c).card=3)
    (two : ∀ c∈P, ordinaryDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) c=2)
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
  have go : g.ordinaryShared.card=2 := by
    rw [fan_ordinary_card n L hL hn tri ht d (mem_filter.mp hdC).1 E (by omega) hi hdC]
    exact two d hd
  omega

theorem certificate_closed_two_or_four_chart {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (P : Finset Point) (sub : P⊆core n L)
    (closed : SharedCoreClosed n L (fun a => ofPredicate n L (tri a) hL (ht a)) P)
    (rigid : ∀ c∈P, (supports n L c).card=3 ∧
      ordinaryDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) c=2 ∧
      (coreDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) c=2 ∨
       coreDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) c=4))
    (c : Point) (hc : c∈P) :
    ∃ f : UpperFan.Sectors n 3 L, f.center=c ∧
      (UpperOpenMathTripleCharts.NormalizedData (fun a => ofPredicate n L (tri a) hL (ht a)) f ∨
       UpperOpenMathAntipodalTwoCapChart.AntipodalData (fun a => ofPredicate n L (tri a) hL (ht a)) f) := by
  classical
  obtain ⟨rc,ac,dc⟩ := rigid c hc
  have zero := certificate_closed_two_cap_zero_marks n L hL hn tri hi ht P sub closed
    (fun p hp => (rigid p hp).1) (fun p hp => (rigid p hp).2.1) c hc
  rcases dc with dc|dc
  · obtain ⟨f,fc,df⟩ := certificate_normalized_two_two_of_zero_marks
      n L hL hn tri hi ht c (sub hc) rc ac dc zero
    exact ⟨f,fc,Or.inl df⟩
  · obtain ⟨f,fc,df⟩ := UpperOpenMathAntipodalTwoCapChart.certificate_antipodal_chart
      n L hL hn tri hi ht c (sub hc) rc ac dc zero
    exact ⟨f,fc,Or.inr df⟩

#print axioms certificate_closed_two_cap_zero_marks
#print axioms certificate_closed_two_or_four_chart
end Kobon.UpperOpenMathClosedTwoCapCharts
