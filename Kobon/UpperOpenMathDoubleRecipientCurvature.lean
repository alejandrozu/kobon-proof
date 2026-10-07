import Kobon.UpperOpenMathTwoThirdCurvature
import Kobon.UpperOpenMathDoubleRecipientWeights
import Kobon.UpperOpenMathNonfullAntipodalRecipients

/-! Actual unrestricted triple curvature with the correction localized to
one-cap degree-three double recipients. There is no component-size bound. -/
namespace Kobon.UpperOpenMathDoubleRecipientCurvature
open Cells FanGeometry UpperVertexBudget UpperTriangleIncidence UpperSharedIncidence
  UpperCoreExtraction UpperOpenMathCapHeavyTriples UpperOpenMathCoreComponents
  UpperOpenMathMarkedPorts UpperOpenMathUnmarkedCrossResources
  UpperOpenMathAntipodalAdjacency UpperOpenMathTwoThirdCurvature Finset
open scoped BigOperators
set_option maxHeartbeats 1000000

theorem certificate_nonfull_recipient_le_two {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (triples : ∀ p∈core n L, (supports n L p).card=3)
    (p : Point) (hp : p∈core n L)
    (small : ordinaryDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) p+
      coreDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) p≤4) :
    recipientCount n L hL hn tri ht p≤2 := by
  let G := fun a => ofPredicate n L (tri a) hL (ht a)
  change ordinaryDegree n L G p+coreDegree n L G p≤4 at small
  change (if ordinaryDegree n L G p+coreDegree n L G p=6 then 0 else
    degreeFrom n L G (unmarkedFullTwoCapSet n L hL hn tri ht) p)≤2
  rw [if_neg (by omega)]
  exact UpperOpenMathNonfullAntipodalRecipients.certificate_nonfull_anti_degree_le_two
    n L hL hn tri hi ht triples p hp small

theorem certificate_double_recipient_core_weight {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (triples : ∀ p∈core n L, (supports n L p).card=3) :
    let G := fun a => ofPredicate n L (tri a) hL (ht a)
    0≤(∑ p∈core n L, (6-2*(ordinaryDegree n L G p : ℤ)-coreDegree n L G p))+
      ((core n L).filter (fun p=>ordinaryDegree n L G p=1 ∧ coreDegree n L G p=5)).card+
      ((core n L).filter (fun p=>ordinaryDegree n L G p=1 ∧ coreDegree n L G p=3 ∧
        recipientCount n L hL hn tri ht p=2)).card-
      3*((core n L).filter (fun p=>ordinaryDegree n L G p=3)).card-
      2*((core n L).filter (fun p=>ordinaryDegree n L G p=2 ∧ coreDegree n L G p=1)).card := by
  have data := certificate_recipient_data n L hL hn tri hi ht triples
  have hpartial (p : Point) (hp : p∈core n L)
      (ap : ordinaryDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) p=2)
      (dp : coreDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) p=1) :
      1≤markedCount n L hL hn tri ht p := by
    have h := marked_count_of_partial_triple n L hL hn tri hi ht p hp (triples p hp) ap dp
    omega
  exact UpperOpenMathDoubleRecipientWeights.finite_double_recipient_curvature_gain
    (core n L) (ordinaryDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)))
    (coreDegree n L (fun a => ofPredicate n L (tri a) hL (ht a))) (markedCount n L hL hn tri ht)
    (recipientCount n L hL hn tri ht) data.ha data.had data.hfive data.hext hpartial data.hx
    (fun p hp small=>certificate_nonfull_recipient_le_two n L hL hn tri hi ht triples p hp small)
    data.hfull data.hbalanced data.capacity data.cone

/-- `J` counts the actual one-cap degree-three recipients of two antipodal sources. -/
theorem certificate_double_recipient_defect_bound {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (triples : ∀ p∈core n L, (supports n L p).card=3) :
    let G := fun a => ofPredicate n L (tri a) hL (ht a)
    2*((n : ℤ)*(n-2)-3*Fintype.card α)+
      ((core n L).filter (fun p=>ordinaryDegree n L G p=1 ∧ coreDegree n L G p=5)).card+
      ((core n L).filter (fun p=>ordinaryDegree n L G p=1 ∧ coreDegree n L G p=3 ∧
        recipientCount n L hL hn tri ht p=2)).card≥
      2*(UpperEdgeInventory.edges n L\usedEdges G).card+
      3*((core n L).filter (fun p=>ordinaryDegree n L G p=3)).card+
      2*((core n L).filter (fun p=>ordinaryDegree n L G p=2 ∧ coreDegree n L G p=1)).card := by
  classical
  let G := fun a => ofPredicate n L (tri a) hL (ht a)
  have weighted := certificate_double_recipient_core_weight n L hL hn tri hi ht triples
  dsimp only at weighted
  have oneNat := UpperOpenMathCoreDoubleCount.one_core_incidence_sum n L hL tri hi ht
  have one : (∑ p∈core n L,(ordinaryDegree n L G p : ℤ))=(oneCoreEdges n L G).card := by exact_mod_cast oneNat
  have twoNat := UpperOpenMathCoreDoubleCount.two_core_incidence_sum n L hL tri ht
  have two : (∑ p∈core n L,(coreDegree n L G p : ℤ))=2*((twoCoreEdges n L G).card : ℤ) := by exact_mod_cast twoNat
  have sumW : (∑ p∈core n L,(6-2*(ordinaryDegree n L G p : ℤ)-coreDegree n L G p))=
      6*((core n L).card : ℤ)-2*(oneCoreEdges n L G).card-2*(twoCoreEdges n L G).card := by
    simp only [sum_sub_distrib,←mul_sum,sum_const,nsmul_eq_mul]
    rw [one,two]
    ring
  have sumLoss : (∑ p∈core n L,(supports n L p).card*((supports n L p).card-2 : ℤ))=
      3*((core n L).card : ℤ) := by
    calc
      _=∑ _p∈core n L,(3 : ℤ) := sum_congr rfl (fun p hp=>by rw [triples p hp]; norm_num)
      _=_ := by simp [sum_const,nsmul_eq_mul,mul_comm]
  have defect := defect_identity n L hL hn tri hi ht
  dsimp only at defect ⊢
  rw [sumLoss] at defect
  rw [sumW] at weighted
  linarith

#print axioms certificate_double_recipient_core_weight
#print axioms certificate_double_recipient_defect_bound
end Kobon.UpperOpenMathDoubleRecipientCurvature
