import Kobon.UpperOpenMathRefinedHalfCurvature
import Kobon.UpperOpenMathOneCapThreeCoreDegree

/-! Actual all-triple half correction. The exceptional N13 recipient is
excluded by the selected-side geometry, so the refined numerical rule has
no remaining J term. No component-size or degree restriction is imposed. -/
namespace Kobon.UpperOpenMathHalfCurvature
open Cells FanGeometry UpperVertexBudget UpperTriangleIncidence UpperSharedIncidence
  UpperCoreExtraction UpperOpenMathCapHeavyTriples UpperOpenMathMarkedPorts
  UpperOpenMathAntipodalAdjacency UpperOpenMathTwoThirdCurvature Finset
open scoped BigOperators
set_option maxHeartbeats 1000000

theorem certificate_recipient_le_two {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (triples : ∀ p∈core n L, (supports n L p).card=3)
    (p : Point) (hp : p∈core n L)
    (ap : ordinaryDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) p=1)
    (dp : coreDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) p=3) :
    recipientCount n L hL hn tri ht p≤2 := by
  let G := fun a => ofPredicate n L (tri a) hL (ht a)
  have ap' : ordinaryDegree n L G p=1 := ap
  have dp' : coreDegree n L G p=3 := dp
  change (if ordinaryDegree n L G p+coreDegree n L G p=6 then 0 else
    UpperOpenMathUnmarkedCrossResources.degreeFrom n L G
      (unmarkedFullTwoCapSet n L hL hn tri ht) p)≤2
  rw [if_neg (by omega)]
  exact UpperOpenMathOneCapThreeCoreDegree.certificate_n13_anti_degree_le_two
    n L hL hn tri hi ht triples p hp ap dp

theorem certificate_triple_recipient_count_zero {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (triples : ∀ p∈core n L, (supports n L p).card=3) :
    let G := fun a => ofPredicate n L (tri a) hL (ht a)
    ((core n L).filter (fun p => ordinaryDegree n L G p=1 ∧ coreDegree n L G p=3 ∧
      recipientCount n L hL hn tri ht p=3)).card=0 := by
  classical
  apply card_eq_zero.mpr
  apply eq_empty_iff_forall_notMem.mpr
  intro p hp
  obtain ⟨hp,ap,dp,xp⟩ := mem_filter.mp hp
  have h := certificate_recipient_le_two n L hL hn tri hi ht triples p hp ap dp
  omega

theorem certificate_half_defect_bound {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (triples : ∀ p∈core n L, (supports n L p).card=3) :
    let G := fun a => ofPredicate n L (tri a) hL (ht a)
    2*((n : ℤ)*(n-2)-3*Fintype.card α)+
      ((unmarkedFullTwoCapSet n L hL hn tri ht).card : ℤ)+
      ((core n L).filter (fun p => ordinaryDegree n L G p=1 ∧ coreDegree n L G p=5)).card≥
      2*(UpperEdgeInventory.edges n L\usedEdges G).card := by
  have h := UpperOpenMathRefinedHalfCurvature.certificate_refined_half_defect_bound
    n L hL hn tri hi ht triples
  have hz := certificate_triple_recipient_count_zero n L hL hn tri hi ht triples
  dsimp only at h hz ⊢
  rw [hz] at h
  simp only [Nat.cast_zero,add_zero] at h
  linarith

#print axioms certificate_recipient_le_two
#print axioms certificate_triple_recipient_count_zero
#print axioms certificate_half_defect_bound
end Kobon.UpperOpenMathHalfCurvature
