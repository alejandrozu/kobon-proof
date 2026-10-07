import Kobon.UpperOpenMathN13Degree
import Kobon.UpperOpenMathN13ActualNoDouble

/-! Actual all-triple curvature after the final double-recipient geometry.
All source-neighbor conditions are derived from the original certificate. -/
namespace Kobon.UpperOpenMathN13Curvature
open Cells FanGeometry UpperVertexBudget UpperTriangleIncidence UpperSharedIncidence
  UpperCoreExtraction UpperOpenMathCapHeavyTriples UpperOpenMathCoreComponents
  UpperOpenMathMarkedPorts UpperOpenMathUnmarkedCrossResources
  UpperOpenMathAntipodalAdjacency UpperOpenMathTwoThirdCurvature
  UpperOpenMathN13Degree Finset
open scoped BigOperators

theorem certificate_no_double_recipients {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (triples : ∀ p∈core n L, (supports n L p).card=3) :
    NoDoubleAntipodalRecipients n L hL hn tri ht := by
  intro p hp ap dp c hc d hd epc epd
  exact UpperOpenMathN13ActualNoDouble.certificate_n13_no_two_anti_neighbors
    n L hL hn tri hi ht triples p hp ap dp c d hc hd epc epd

theorem certificate_n13_anti_degree_le_one {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (triples : ∀ p∈core n L, (supports n L p).card=3)
    (p : Point) (hp : p∈core n L)
    (ap : ordinaryDegree n L (fun a=>ofPredicate n L (tri a) hL (ht a)) p=1)
    (dp : coreDegree n L (fun a=>ofPredicate n L (tri a) hL (ht a)) p=3) :
    degreeFrom n L (fun a=>ofPredicate n L (tri a) hL (ht a))
      (unmarkedFullTwoCapSet n L hL hn tri ht) p≤1 :=
  certificate_n13_degree_le_one_of_unique n L hL hn tri ht
    (certificate_no_double_recipients n L hL hn tri hi ht triples) p hp ap dp

theorem certificate_source_free_defect_bound {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (triples : ∀ p∈core n L, (supports n L p).card=3) :
    let G := fun a=>ofPredicate n L (tri a) hL (ht a)
    2*((n : ℤ)*(n-2)-3*Fintype.card α)+
      ((core n L).filter (fun p=>ordinaryDegree n L G p=1 ∧ coreDegree n L G p=5)).card≥
      2*(UpperEdgeInventory.edges n L\usedEdges G).card+
      3*((core n L).filter (fun p=>ordinaryDegree n L G p=3)).card+
      3*((core n L).filter (fun p=>ordinaryDegree n L G p=2 ∧ coreDegree n L G p=1)).card :=
  certificate_no_source_correction_of_unique n L hL hn tri hi ht triples
    (certificate_no_double_recipients n L hL hn tri hi ht triples)

theorem certificate_closed_source_free_gain {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (triples : ∀ p∈core n L, (supports n L p).card=3)
    (P : Finset Point) (sub : P⊆core n L)
    (closed : SharedCoreClosed n L (fun a=>ofPredicate n L (tri a) hL (ht a)) P) :
    let G := fun a=>ofPredicate n L (tri a) hL (ht a)
    0≤2*componentCost n L G P+
      ((P.filter (fun p=>ordinaryDegree n L G p=1 ∧ coreDegree n L G p=5)).card : ℤ)-
      3*((P.filter (fun p=>ordinaryDegree n L G p=3)).card : ℤ)-
      3*((P.filter (fun p=>ordinaryDegree n L G p=2 ∧ coreDegree n L G p=1)).card : ℤ) :=
  certificate_closed_no_source_gain_of_unique n L hL hn tri hi ht triples
    (certificate_no_double_recipients n L hL hn tri hi ht triples) P sub closed

theorem certificate_source_free_hybrid_component_defect {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (triples : ∀ p∈core n L, (supports n L p).card=3) :
    let G := fun a=>ofPredicate n L (tri a) hL (ht a)
    (UpperEdgeInventory.edges n L\usedEdges G).card+
      (∑ s∈components n L G,unrestrictedLowerOn n L hL hn tri ht (componentVertices n L G s))≤
      (n : ℤ)*(n-2)-3*Fintype.card α :=
  certificate_hybrid_no_source_component_defect_of_unique n L hL hn tri hi ht triples
    (certificate_no_double_recipients n L hL hn tri hi ht triples)

#print axioms certificate_no_double_recipients
#print axioms certificate_n13_anti_degree_le_one
#print axioms certificate_source_free_defect_bound
#print axioms certificate_closed_source_free_gain
#print axioms certificate_source_free_hybrid_component_defect
end Kobon.UpperOpenMathN13Curvature
