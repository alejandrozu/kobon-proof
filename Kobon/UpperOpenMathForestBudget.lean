import Kobon.UpperOpenMathCoreComponents
import Kobon.UpperOpenMathTripleCapBudget
import Kobon.UpperOpenMathCoreGraphCounts
import Kobon.UpperOpenMathMixedCapBudget
import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-! Actual forest identities and the triple-cap defect correction. -/
namespace Kobon.UpperOpenMathForestBudget
open Cells FanGeometry UpperVertexBudget UpperTriangleIncidence UpperSharedIncidence
  UpperCoreExtraction UpperOpenMathCapHeavyTriples UpperOpenMathCoreComponents Finset
open scoped BigOperators

theorem acyclic_component_card {V : Type*} [Finite V] (H : SimpleGraph V)
    (acyclic : H.IsAcyclic) (s : H.ConnectedComponent) :
    Nat.card s.toSimpleGraph.edgeSet+1=Nat.card s.supp := by
  classical
  letI : Fintype s.supp := Fintype.ofFinite _
  letI : Fintype s.toSimpleGraph.edgeSet := Fintype.ofFinite _
  have tree : s.toSimpleGraph.IsTree :=
    ⟨s.connected_toSimpleGraph,acyclic.induce s.supp⟩
  have h := tree.card_edgeFinset
  rw [Nat.card_eq_fintype_card,Nat.card_eq_fintype_card,← SimpleGraph.edgeFinset_card]
  exact h

theorem certificate_forest_edge_component_count {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L)
    (tri : α → Triple) (ht : ∀ a, TrianglePredicate n L (tri a))
    (forest : (coreGraph n L (fun a => ofPredicate n L (tri a) hL (ht a))).IsAcyclic) :
    let G := fun a => ofPredicate n L (tri a) hL (ht a)
    (twoCoreEdges n L G).card+coreComponentCount n L G=(core n L).card := by
  classical
  let G := fun a => ofPredicate n L (tri a) hL (ht a)
  have hEach (s : (coreGraph n L G).ConnectedComponent) (hs : s∈components n L G) :
      (componentEdges n L G (componentVertices n L G s)).card+1=(componentVertices n L G s).card := by
    have h := acyclic_component_card (coreGraph n L G) forest s
    rw [UpperOpenMathCoreGraphCounts.certificate_component_edge_card n L hL tri ht s,
      component_support_card] at h
    exact h
  have hSum := sum_congr rfl hEach
  rw [sum_add_distrib] at hSum
  have hE := component_edges_sum n L hL tri ht
  dsimp only at hE
  change (∑ s∈components n L G, (componentEdges n L G (componentVertices n L G s)).card)=
    (twoCoreEdges n L G).card at hE
  rw [hE,component_vertices_sum] at hSum
  simp only [sum_const,nsmul_eq_mul,mul_one,components_card] at hSum
  exact hSum

theorem certificate_triple_forest_bound {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (triples : ∀ p∈core n L, (supports n L p).card=3)
    (forest : (coreGraph n L (fun a => ofPredicate n L (tri a) hL (ht a))).IsAcyclic) :
    let G := fun a => ofPredicate n L (tri a) hL (ht a)
    3*(Fintype.card α : ℤ)+(UpperEdgeInventory.edges n L\usedEdges G).card+
      coreComponentCount n L G+
      2*((core n L).filter (fun p => ordinaryDegree n L G p=3)).card+
      ((core n L).filter (fun p => ordinaryDegree n L G p=2 ∧ coreDegree n L G p=1)).card≤
      (n : ℤ)*(n-2) := by
  classical
  let G := fun a => ofPredicate n L (tri a) hL (ht a)
  have h := UpperOpenMathTripleCapBudget.certificate_triple_cap_defect n L hL hn tri hi ht triples
  have hE := certificate_forest_edge_component_count n L hL tri ht forest
  have hEZ : ((twoCoreEdges n L G).card : ℤ)+coreComponentCount n L G=(core n L).card := by
    exact_mod_cast hE
  dsimp only at h
  change 3*(Fintype.card α : ℤ)+(UpperEdgeInventory.edges n L\usedEdges G).card+
    coreComponentCount n L G+2*((core n L).filter (fun p => ordinaryDegree n L G p=3)).card+
    ((core n L).filter (fun p => ordinaryDegree n L G p=2 ∧ coreDegree n L G p=1)).card≤(n : ℤ)*(n-2)
  linarith

theorem certificate_mixed_forest_weighted_bound {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (forest : (coreGraph n L (fun a => ofPredicate n L (tri a) hL (ht a))).IsAcyclic) :
    let G := fun a => ofPredicate n L (tri a) hL (ht a)
    9*(Fintype.card α : ℤ)+3*(UpperEdgeInventory.edges n L\usedEdges G).card+
      3*coreComponentCount n L G+3*UpperOpenMathMixedCapBudget.higherWeight n L+
      2*(∑ p∈UpperOpenMathMixedCapBudget.poorTripleCores n L G, (coreDegree n L G p : ℤ))≤
      3*(n : ℤ)*(n-2) := by
  classical
  let G := fun a => ofPredicate n L (tri a) hL (ht a)
  have h := UpperOpenMathMixedCapBudget.certificate_mixed_weighted_defect n L hL hn tri hi ht
  have hE := certificate_forest_edge_component_count n L hL tri ht forest
  have hEZ : ((twoCoreEdges n L G).card : ℤ)+coreComponentCount n L G=(core n L).card := by
    exact_mod_cast hE
  dsimp only at h
  change 9*(Fintype.card α : ℤ)+3*(UpperEdgeInventory.edges n L\usedEdges G).card+
    3*coreComponentCount n L G+3*UpperOpenMathMixedCapBudget.higherWeight n L+
    2*(∑ p∈UpperOpenMathMixedCapBudget.poorTripleCores n L G, (coreDegree n L G p : ℤ))≤3*(n : ℤ)*(n-2)
  linarith

theorem certificate_mixed_forest_bound {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (forest : (coreGraph n L (fun a => ofPredicate n L (tri a) hL (ht a))).IsAcyclic) :
    let G := fun a => ofPredicate n L (tri a) hL (ht a)
    3*(Fintype.card α : ℤ)+(UpperEdgeInventory.edges n L\usedEdges G).card+
      coreComponentCount n L G+UpperOpenMathMixedCapBudget.higherWeight n L≤(n : ℤ)*(n-2) := by
  classical
  let G := fun a => ofPredicate n L (tri a) hL (ht a)
  have h := UpperOpenMathMixedCapBudget.certificate_mixed_core_defect n L hL hn tri hi ht
  have hE := certificate_forest_edge_component_count n L hL tri ht forest
  have hEZ : ((twoCoreEdges n L G).card : ℤ)+coreComponentCount n L G=(core n L).card := by
    exact_mod_cast hE
  dsimp only at h
  change 3*(Fintype.card α : ℤ)+(UpperEdgeInventory.edges n L\usedEdges G).card+
    coreComponentCount n L G+UpperOpenMathMixedCapBudget.higherWeight n L≤(n : ℤ)*(n-2)
  linarith

theorem certificate_mixed_forest_count_bound {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (forest : (coreGraph n L (fun a => ofPredicate n L (tri a) hL (ht a))).IsAcyclic) :
    let G := fun a => ofPredicate n L (tri a) hL (ht a)
    3*(Fintype.card α : ℤ)+(UpperEdgeInventory.edges n L\usedEdges G).card+
      coreComponentCount n L G+(UpperOpenMathMixedCapBudget.higherCores n L).card≤(n : ℤ)*(n-2) := by
  have h := certificate_mixed_forest_bound n L hL hn tri hi ht forest
  have hA := UpperOpenMathMixedCapBudget.higher_weight_ge_card n L
  dsimp only at h ⊢
  linarith

#print axioms acyclic_component_card
#print axioms certificate_forest_edge_component_count
#print axioms certificate_triple_forest_bound
#print axioms certificate_mixed_forest_weighted_bound
#print axioms certificate_mixed_forest_bound
end Kobon.UpperOpenMathForestBudget
