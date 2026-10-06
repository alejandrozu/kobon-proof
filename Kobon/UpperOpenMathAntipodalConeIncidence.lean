import Kobon.UpperOpenMathAntipodalFullNeighborPair

/-! Actual bipartite edge resources forced by antipodal two-cap cones.
Every such center has two nonfull neighbors in the all-triple class. Their
incidences consume two separate cross edges per center. Recipient capacities
and any final curvature discharging remain distinct obligations.
-/
namespace Kobon.UpperOpenMathAntipodalConeIncidence
open Cells UpperVertexBudget UpperTriangleIncidence UpperSharedIncidence
  UpperCoreExtraction UpperOpenMathAntipodalAdjacency
  UpperOpenMathAntipodalFullNeighborPair Finset
open scoped BigOperators

noncomputable def crossEdges {β : Type*} [DecidableEq β]
    (E : Finset (Finset β)) (A B : Finset β) : Finset (Finset β) :=
  E.filter fun e=>(e∩A).Nonempty ∧ (e∩B).Nonempty

theorem cross_left_independent {β : Type*} [DecidableEq β]
    (E : Finset (Finset β)) (A B : Finset β) (disj : Disjoint A B)
    (cards : ∀ e∈E, e.card=2) :
    ∀ e∈crossEdges E A B, ∀ p∈e∩A, ∀ q∈e∩A, p=q := by
  intro e he p hp q hq
  obtain ⟨he,_,b,hb⟩ := mem_filter.mp he
  by_contra hpq
  have hpE := (mem_inter.mp hp).1
  have hpA := (mem_inter.mp hp).2
  have hqE := (mem_inter.mp hq).1
  have hqA := (mem_inter.mp hq).2
  have hbE := (mem_inter.mp hb).1
  have hbB := (mem_inter.mp hb).2
  have hpb : p≠b := fun hh=>disjoint_left.mp disj hpA (by simpa only [←hh] using hbB)
  have hqb : q≠b := fun hh=>disjoint_left.mp disj hqA (by simpa only [←hh] using hbB)
  have sub : ({p,q,b} : Finset β)⊆e := by
    intro x hx
    rcases (by simpa only [mem_insert,mem_singleton] using hx : x=p∨x=q∨x=b) with rfl|rfl|rfl
    all_goals assumption
  have hc := card_le_card sub
  have hc3 : ({p,q,b} : Finset β).card=3 := by simp [hpq,hpb,hqb]
  rw [hc3,cards e he] at hc
  omega

theorem pair_right_injective {β : Type*} [DecidableEq β] (c : β) :
    Function.Injective (fun q=>({c,q} : Finset β)) := by
  intro p q he
  change ({c,p} : Finset β)={c,q} at he
  have hp : p∈({c,q} : Finset β) := by rw [←he]; simp
  have hq : q∈({c,p} : Finset β) := by rw [he]; simp
  simp only [mem_insert,mem_singleton] at hp hq
  rcases hp with hp|hp
  · rcases hq with hq|hq
    · exact hp.trans hq.symm
    · exact hq.symm
  · exact hp

theorem neighbor_card_le_cross_degree {β : Type*} [DecidableEq β]
    (E : Finset (Finset β)) (A B : Finset β) (c : β) (hc : c∈A) :
    (B.filter (fun q=>{c,q}∈E)).card≤
      ((crossEdges E A B).filter (fun e=>c∈e)).card := by
  let S := B.filter fun q=>{c,q}∈E
  have sub : S.image (fun q=>({c,q} : Finset β))⊆
      (crossEdges E A B).filter (fun e=>c∈e) := by
    intro e he
    obtain ⟨q,hq,rfl⟩ := mem_image.mp he
    obtain ⟨hqB,hqE⟩ := mem_filter.mp hq
    apply mem_filter.mpr
    refine ⟨mem_filter.mpr ⟨hqE,?_,?_⟩,by simp⟩
    · exact ⟨c,mem_inter.mpr ⟨by simp,hc⟩⟩
    · exact ⟨q,mem_inter.mpr ⟨by simp,hqB⟩⟩
  have h := card_le_card sub
  rw [card_image_of_injective S (pair_right_injective c)] at h
  exact h

theorem two_cone_edge_budget {β : Type*} [DecidableEq β]
    (E : Finset (Finset β)) (A B : Finset β) (disj : Disjoint A B)
    (cards : ∀ e∈E, e.card=2)
    (neighbors : ∀ c∈A, 2≤(B.filter (fun q=>{c,q}∈E)).card) :
    2*A.card≤(crossEdges E A B).card := by
  have hsum : (∑ c∈A,2)≤
      ∑ c∈A,((crossEdges E A B).filter (fun e=>c∈e)).card := by
    apply sum_le_sum
    intro c hc
    exact (neighbors c hc).trans (neighbor_card_le_cross_degree E A B c hc)
  have hcross := UpperOpenMathTripleGraph.independent_incidence_bound
    (crossEdges E A B) A (cross_left_independent E A B disj cards)
  have h := hsum.trans hcross
  simpa [Nat.mul_comm] using h

noncomputable def nonfullCoreSet {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (G : α → TriangleGeometry) : Finset Point := by
  classical
  exact (core n L).filter fun q=>¬FullAt n L G q

/-- No assumption about independent recipient cones is made. -/
theorem certificate_two_anti_le_nonfull_cross_edges {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (triples : ∀ c∈core n L, (supports n L c).card=3) :
    let G := fun a => ofPredicate n L (tri a) hL (ht a)
    2*(unmarkedFullTwoCapSet n L hL hn tri ht).card≤
      (crossEdges (twoCoreEdges n L G) (unmarkedFullTwoCapSet n L hL hn tri ht)
        (nonfullCoreSet n L G)).card := by
  classical
  let G := fun a => ofPredicate n L (tri a) hL (ht a)
  let A := unmarkedFullTwoCapSet n L hL hn tri ht
  let N := nonfullCoreSet n L G
  apply two_cone_edge_budget (twoCoreEdges n L G) A N
  · apply disjoint_left.mpr
    intro c hc hn
    obtain ⟨hcC,ac,dc,mc⟩ := mem_filter.mp hc
    obtain ⟨_,nonfull⟩ := mem_filter.mp hn
    change UpperOpenMathCapHeavyTriples.ordinaryDegree n L G c=2 at ac
    change UpperOpenMathCapHeavyTriples.coreDegree n L G c=4 at dc
    apply nonfull
    change UpperOpenMathCapHeavyTriples.ordinaryDegree n L G c+
      UpperOpenMathCapHeavyTriples.coreDegree n L G c=6
    omega
  · intro e he
    exact used_edge_card G (mem_filter.mp (mem_sdiff.mp he).1).1
  · intro c hc
    obtain ⟨hcC,ac,dc,mc⟩ := mem_filter.mp hc
    have h := certificate_two_nonfull_or_higher_neighbors n L hL hn tri hi ht
      c hcC (triples c hcC) ac dc mc
    have eq : nonFullTripleNeighbors n L G c=N.filter (fun q=>{c,q}∈twoCoreEdges n L G) := by
      ext q
      simp only [nonFullTripleNeighbors,N,nonfullCoreSet,mem_filter]
      by_cases hq : q∈core n L
      · have rq := triples q hq
        simp [hq,FullTripleAt,rq,and_comm]
      · simp [hq]
    rw [eq] at h
    exact h

#print axioms two_cone_edge_budget
#print axioms certificate_two_anti_le_nonfull_cross_edges
end Kobon.UpperOpenMathAntipodalConeIncidence
