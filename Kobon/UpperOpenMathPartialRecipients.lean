import Kobon.UpperOpenMathClosedDoubleRecipientCurvature

/-! A partial two-cap source sends its only shared core side to a poor
target. It therefore receives no unmarked full two-cap source. -/
namespace Kobon.UpperOpenMathPartialRecipients
open Cells FanGeometry UpperVertexBudget UpperTriangleIncidence UpperSharedIncidence
  UpperCoreExtraction UpperOpenMathCapHeavyTriples UpperOpenMathCoreComponents
  UpperOpenMathMarkedPorts UpperOpenMathUnmarkedCrossResources
  UpperOpenMathAntipodalAdjacency UpperOpenMathTwoThirdCurvature Finset
set_option maxHeartbeats 1000000

theorem certificate_partial_anti_degree_zero {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (triples : ∀ p∈core n L, (supports n L p).card=3)
    (p : Point) (hp : p∈core n L)
    (ap : ordinaryDegree n L (fun a=>ofPredicate n L (tri a) hL (ht a)) p=2)
    (dp : coreDegree n L (fun a=>ofPredicate n L (tri a) hL (ht a)) p=1) :
    degreeFrom n L (fun a=>ofPredicate n L (tri a) hL (ht a))
      (unmarkedFullTwoCapSet n L hL hn tri ht) p=0 := by
  classical
  let G := fun a=>ofPredicate n L (tri a) hL (ht a)
  unfold degreeFrom
  apply card_eq_zero.mpr
  apply eq_empty_iff_forall_notMem.mpr
  intro e he
  obtain ⟨he,hpe,q,hq⟩ := mem_filter.mp he
  obtain ⟨hqe,hqA⟩ := mem_inter.mp hq
  obtain ⟨hqC,aq,dq,mq⟩ := mem_filter.mp hqA
  have ne : p≠q := by
    intro eq
    change coreDegree n L G q=4 at dq
    change coreDegree n L G p=1 at dp
    rw [eq] at dp
    omega
  have pair : e={p,q} := by
    apply Eq.symm
    apply eq_of_subset_of_card_le
    · intro r hr
      rcases mem_insert.mp hr with hr|hr
      · simpa only [hr] using hpe
      · simpa only [mem_singleton.mp hr] using hqe
    · rw [card_pair ne,used_edge_card G (mem_filter.mp (mem_sdiff.mp he).1).1]
  have poor := UpperOpenMathMarkedPoverty.certificate_cap_heavy_neighbor_sum
    n L hL hn tri hi ht p q hp hqC (triples p hp) (triples q hqC) (Or.inr ⟨ap,dp⟩)
    (by simpa only [pair] using he)
  change ordinaryDegree n L G q≤1 ∧ _ at poor
  change ordinaryDegree n L G q=2 at aq
  omega

theorem certificate_partial_recipient_zero {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (triples : ∀ p∈core n L, (supports n L p).card=3)
    (p : Point) (hp : p∈core n L)
    (ap : ordinaryDegree n L (fun a=>ofPredicate n L (tri a) hL (ht a)) p=2)
    (dp : coreDegree n L (fun a=>ofPredicate n L (tri a) hL (ht a)) p=1) :
    recipientCount n L hL hn tri ht p=0 := by
  unfold recipientCount
  dsimp only
  rw [if_neg (by rw [ap,dp]; decide)]
  exact certificate_partial_anti_degree_zero n L hL hn tri hi ht triples p hp ap dp

theorem certificate_closed_partial_recipient_zero {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (triples : ∀ p∈core n L, (supports n L p).card=3)
    (P : Finset Point) (sub : P⊆core n L)
    (p : Point) (hp : p∈P)
    (ap : ordinaryDegree n L (fun a=>ofPredicate n L (tri a) hL (ht a)) p=2)
    (dp : coreDegree n L (fun a=>ofPredicate n L (tri a) hL (ht a)) p=1) :
    UpperOpenMathClosedDoubleRecipientCurvature.closedRecipientCount n L hL hn tri ht P p=0 := by
  classical
  let G := fun a=>ofPredicate n L (tri a) hL (ht a)
  let A := P.filter (fun q=>ordinaryDegree n L G q=2 ∧ coreDegree n L G q=4 ∧ markedCount n L hL hn tri ht q=0)
  have aSub : A⊆unmarkedFullTwoCapSet n L hL hn tri ht := by
    intro q hq
    obtain ⟨hq,hpred⟩ := mem_filter.mp hq
    exact mem_filter.mpr ⟨sub hq,hpred⟩
  have bound := degreeFrom_mono n L G A (unmarkedFullTwoCapSet n L hL hn tri ht) aSub p
  have zero := certificate_partial_anti_degree_zero n L hL hn tri hi ht triples p (sub hp) ap dp
  change degreeFrom n L G (unmarkedFullTwoCapSet n L hL hn tri ht) p=0 at zero
  have localZero : degreeFrom n L G A p=0 := by omega
  change (if ordinaryDegree n L G p+coreDegree n L G p=6 then 0 else degreeFrom n L G A p)=0
  split_ifs <;> simp only [localZero]

#print axioms certificate_partial_anti_degree_zero
#print axioms certificate_partial_recipient_zero
#print axioms certificate_closed_partial_recipient_zero
end Kobon.UpperOpenMathPartialRecipients
