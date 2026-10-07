import Kobon.UpperOpenMathAntipodalConeIncidence
import Kobon.UpperOpenMathUnmarkedCrossResources

/-! The actual antipodal cone budget stays inside every shared-core closed
subset, allowing componentwise discharging. -/
namespace Kobon.UpperOpenMathClosedConeIncidence
open Cells FanGeometry UpperVertexBudget UpperTriangleIncidence UpperSharedIncidence
  UpperCoreExtraction UpperOpenMathCapHeavyTriples UpperOpenMathCoreComponents
  UpperOpenMathAntipodalFullNeighborPair Finset
open scoped BigOperators

theorem certificate_closed_two_anti_cone {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (triples : ∀ p∈core n L, (supports n L p).card=3)
    (P : Finset Point) (sub : P⊆core n L)
    (closed : SharedCoreClosed n L (fun a => ofPredicate n L (tri a) hL (ht a)) P) :
    let G := fun a => ofPredicate n L (tri a) hL (ht a)
    let A := P.filter (fun p => ordinaryDegree n L G p=2 ∧ coreDegree n L G p=4 ∧
      UpperOpenMathMarkedPorts.markedCount n L hL hn tri ht p=0)
    let N := P.filter (fun p => ordinaryDegree n L G p+coreDegree n L G p≠6)
    2*A.card≤(UpperOpenMathUnmarkedCrossResources.crossEdges n L G A N).card := by
  classical
  let G := fun a => ofPredicate n L (tri a) hL (ht a)
  let A := P.filter (fun p => ordinaryDegree n L G p=2 ∧ coreDegree n L G p=4 ∧
    UpperOpenMathMarkedPorts.markedCount n L hL hn tri ht p=0)
  let N := P.filter (fun p => ordinaryDegree n L G p+coreDegree n L G p≠6)
  change 2*A.card≤(UpperOpenMathAntipodalConeIncidence.crossEdges (twoCoreEdges n L G) A N).card
  apply UpperOpenMathAntipodalConeIncidence.two_cone_edge_budget (twoCoreEdges n L G) A N
  · apply disjoint_left.mpr
    intro p hpA hpN
    obtain ⟨_,ap,dp,mp⟩ := mem_filter.mp hpA
    have noFull := (mem_filter.mp hpN).2
    change ordinaryDegree n L G p=2 at ap
    change coreDegree n L G p=4 at dp
    omega
  · intro e he
    exact used_edge_card G (mem_filter.mp (mem_sdiff.mp he).1).1
  · intro c hc
    obtain ⟨hcP,ac,dc,mc⟩ := mem_filter.mp hc
    have bound := certificate_two_nonfull_or_higher_neighbors n L hL hn tri hi ht
      c (sub hcP) (triples c (sub hcP)) ac dc mc
    have eq : nonFullTripleNeighbors n L G c=N.filter (fun q => {c,q}∈twoCoreEdges n L G) := by
      ext q
      constructor
      · intro hq
        obtain ⟨hqCore,edge,noFull⟩ := mem_filter.mp hq
        have qp : q∈P := closed {c,q} edge c (by simp) hcP (by simp)
        have nf : ordinaryDegree n L G q+coreDegree n L G q≠6 :=
          fun full => noFull ⟨triples q hqCore,full⟩
        exact mem_filter.mpr ⟨mem_filter.mpr ⟨qp,nf⟩,edge⟩
      · intro hq
        obtain ⟨hqN,edge⟩ := mem_filter.mp hq
        obtain ⟨hqP,nf⟩ := mem_filter.mp hqN
        exact mem_filter.mpr ⟨sub hqP,edge,fun full => nf full.2⟩
    rw [eq] at bound
    exact bound

#print axioms certificate_closed_two_anti_cone
end Kobon.UpperOpenMathClosedConeIncidence
