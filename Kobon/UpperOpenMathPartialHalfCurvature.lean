import Kobon.UpperOpenMathHalfCurvature
import Kobon.UpperOpenMathPartialHalfGainWeights
import Kobon.UpperOpenMathPartialRecipients

/-! A stronger actual all-triple charging theorem retaining the positive
three-cap and partial two-cap terms. Actual N13 geometry eliminates the
intermediate J term in the final endpoint. -/
namespace Kobon.UpperOpenMathPartialHalfCurvature
open Cells FanGeometry UpperVertexBudget UpperTriangleIncidence UpperSharedIncidence
  UpperCoreExtraction UpperOpenMathCapHeavyTriples UpperOpenMathCoreComponents
  UpperOpenMathMarkedPorts UpperOpenMathUnmarkedCrossResources
  UpperOpenMathAntipodalAdjacency UpperOpenMathTwoThirdCurvature Finset
open scoped BigOperators
set_option maxHeartbeats 1000000

theorem certificate_partial_half_core_weight {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (triples : ∀ p∈core n L, (supports n L p).card=3) :
    let G := fun a => ofPredicate n L (tri a) hL (ht a)
    0≤2*(∑ p∈core n L, (6-2*(ordinaryDegree n L G p : ℤ)-coreDegree n L G p))+
      2*((unmarkedFullTwoCapSet n L hL hn tri ht).card : ℤ)+
      2*((core n L).filter (fun p => ordinaryDegree n L G p=1 ∧ coreDegree n L G p=5)).card+
      ((core n L).filter (fun p => ordinaryDegree n L G p=1 ∧ coreDegree n L G p=3 ∧
        recipientCount n L hL hn tri ht p=3)).card-
      6*((core n L).filter (fun p => ordinaryDegree n L G p=3)).card-
      6*((core n L).filter (fun p => ordinaryDegree n L G p=2 ∧ coreDegree n L G p=1)).card := by
  have data := certificate_recipient_data n L hL hn tri hi ht triples
  have hpartial (p : Point) (hp : p∈core n L)
      (ap : ordinaryDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) p=2)
      (dp : coreDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) p=1) :
      1≤markedCount n L hL hn tri ht p := by
    have h := marked_count_of_partial_triple n L hL hn tri hi ht p hp (triples p hp) ap dp
    omega
  exact UpperOpenMathPartialHalfGainWeights.finite_partial_half_curvature_gain
    (core n L) (ordinaryDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)))
    (coreDegree n L (fun a => ofPredicate n L (tri a) hL (ht a))) (markedCount n L hL hn tri ht)
    (recipientCount n L hL hn tri ht) data.ha data.had data.hfive data.hext hpartial
    (fun p hp ap dp=>UpperOpenMathPartialRecipients.certificate_partial_recipient_zero n L hL hn tri hi ht triples p hp ap dp) data.hx data.hfull
    data.hbalanced data.capacity data.cone

theorem certificate_refined_partial_half_defect_bound {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (triples : ∀ p∈core n L, (supports n L p).card=3) :
    let G := fun a => ofPredicate n L (tri a) hL (ht a)
    4*((n : ℤ)*(n-2)-3*Fintype.card α)+
      2*((unmarkedFullTwoCapSet n L hL hn tri ht).card : ℤ)+
      2*((core n L).filter (fun p => ordinaryDegree n L G p=1 ∧ coreDegree n L G p=5)).card+
      ((core n L).filter (fun p => ordinaryDegree n L G p=1 ∧ coreDegree n L G p=3 ∧
        recipientCount n L hL hn tri ht p=3)).card≥
      4*(UpperEdgeInventory.edges n L\usedEdges G).card+
      6*((core n L).filter (fun p => ordinaryDegree n L G p=3)).card+
      6*((core n L).filter (fun p => ordinaryDegree n L G p=2 ∧ coreDegree n L G p=1)).card := by
  classical
  let G := fun a => ofPredicate n L (tri a) hL (ht a)
  have weighted := certificate_partial_half_core_weight n L hL hn tri hi ht triples
  dsimp only at weighted
  have oneNat := UpperOpenMathCoreDoubleCount.one_core_incidence_sum n L hL tri hi ht
  have one : (∑ p∈core n L,(ordinaryDegree n L G p : ℤ))=(oneCoreEdges n L G).card := by exact_mod_cast oneNat
  have twoNat := UpperOpenMathCoreDoubleCount.two_core_incidence_sum n L hL tri ht
  have two : (∑ p∈core n L,(coreDegree n L G p : ℤ))=2*((twoCoreEdges n L G).card : ℤ) := by exact_mod_cast twoNat
  have sumW : (∑ p∈core n L,(6-2*(ordinaryDegree n L G p : ℤ)-coreDegree n L G p))=
      6*((core n L).card : ℤ)-2*(oneCoreEdges n L G).card-2*(twoCoreEdges n L G).card := by
    simp only [sum_sub_distrib,← mul_sum,sum_const,nsmul_eq_mul]
    rw [one,two]
    ring
  have sumLoss : (∑ p∈core n L,(supports n L p).card*((supports n L p).card-2 : ℤ))=
      3*((core n L).card : ℤ) := by
    calc
      _=∑ _p∈core n L,(3 : ℤ) := sum_congr rfl (fun p hp => by rw [triples p hp]; norm_num)
      _=_ := by simp [sum_const,nsmul_eq_mul,mul_comm]
  have defect := defect_identity n L hL hn tri hi ht
  dsimp only at defect ⊢
  rw [sumLoss] at defect
  rw [sumW] at weighted
  linarith

theorem certificate_partial_half_defect_bound {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (triples : ∀ p∈core n L, (supports n L p).card=3) :
    let G := fun a => ofPredicate n L (tri a) hL (ht a)
    4*((n : ℤ)*(n-2)-3*Fintype.card α)+
      2*((unmarkedFullTwoCapSet n L hL hn tri ht).card : ℤ)+
      2*((core n L).filter (fun p => ordinaryDegree n L G p=1 ∧ coreDegree n L G p=5)).card≥
      4*(UpperEdgeInventory.edges n L\usedEdges G).card+
      6*((core n L).filter (fun p => ordinaryDegree n L G p=3)).card+
      6*((core n L).filter (fun p => ordinaryDegree n L G p=2 ∧ coreDegree n L G p=1)).card := by
  have h := certificate_refined_partial_half_defect_bound n L hL hn tri hi ht triples
  have hz := UpperOpenMathHalfCurvature.certificate_triple_recipient_count_zero n L hL hn tri hi ht triples
  dsimp only at h hz ⊢
  rw [hz] at h
  simpa only [Nat.cast_zero,add_zero] using h

#print axioms certificate_partial_half_core_weight
#print axioms certificate_partial_half_defect_bound
end Kobon.UpperOpenMathPartialHalfCurvature
