import Kobon.UpperOpenMathN12Curvature

/-! Outgoing marked ports and incoming antipodal-source edges consume
disjoint actual shared-core slots at each triple core. -/
namespace Kobon.UpperOpenMathLocalPortBudget
open Cells FanGeometry UpperVertexBudget UpperTriangleIncidence UpperSharedIncidence
  UpperCoreExtraction UpperOpenMathCapHeavyTriples UpperOpenMathMarkedPorts
  UpperOpenMathUnmarkedCrossResources UpperOpenMathAntipodalAdjacency Finset

theorem certificate_marked_plus_anti_degree_le {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (triples : ∀ p∈core n L, (supports n L p).card=3)
    (p : Point) (hp : p∈core n L) :
    markedCount n L hL hn tri ht p+
      degreeFrom n L (fun a=>ofPredicate n L (tri a) hL (ht a))
        (unmarkedFullTwoCapSet n L hL hn tri ht) p≤
      coreDegree n L (fun a=>ofPredicate n L (tri a) hL (ht a)) p := by
  classical
  let G := fun a=>ofPredicate n L (tri a) hL (ht a)
  let A := unmarkedFullTwoCapSet n L hL hn tri ht
  by_cases pa : p∈A
  · have zero := (mem_filter.mp pa).2.2.2
    change markedCount n L hL hn tri ht p=0 at zero
    rw [zero,Nat.zero_add]
    exact degreeFrom_le n L G A p
  · let M := markedEdges n L hL hn tri ht p
    let N := (twoCoreEdges n L G).filter (fun e=>p∈e ∧ (e∩A).Nonempty)
    let I := (twoCoreEdges n L G).filter (fun e=>p∈e)
    have mSub : M⊆I := by
      intro e he
      have sp := marked_edge_spec n L hL hn tri hi ht triples p hp e he
      exact mem_filter.mpr ⟨sp.1,sp.2.1⟩
    have nSub : N⊆I := by
      intro e he
      exact mem_filter.mpr ⟨(mem_filter.mp he).1,(mem_filter.mp he).2.1⟩
    have dis : Disjoint M N := by
      apply disjoint_left.mpr
      intro e hem hen
      have sp := marked_edge_spec n L hL hn tri hi ht triples p hp e hem
      obtain ⟨he,hpe,q,hq⟩ := mem_filter.mp hen
      obtain ⟨hqe,hqA⟩ := mem_inter.mp hq
      have qne : q≠p := by intro eq; exact pa (by simpa only [eq] using hqA)
      have poor := sp.2.2.2 q hqe qne
      have low := (mem_filter.mp poor).2.2.1
      have high := (mem_filter.mp hqA).2.1
      change ordinaryDegree n L G q≤1 at low
      change ordinaryDegree n L G q=2 at high
      omega
    have uSub : M∪N⊆I := by
      intro e he
      rcases mem_union.mp he with he|he
      · exact mSub he
      · exact nSub he
    have bound := card_le_card uSub
    rw [card_union_of_disjoint dis] at bound
    exact bound

#print axioms certificate_marked_plus_anti_degree_le
end Kobon.UpperOpenMathLocalPortBudget
