import Kobon.UpperOpenMathTripleDegreeThree
import Kobon.UpperOpenMathCoreDegree
import Kobon.UpperOpenMathMixedDegreeThree

/-! Perfect triangle counts exclude up to three multiple points of any
multiplicity, or up to four triple points. These are actual straight-line
certificate statements, with no local-fan or graph-count assumptions. -/
namespace Kobon.UpperOpenMathSmallCoreRigidity
open Cells FanGeometry UpperVertexBudget UpperTriangleIncidence UpperSharedIncidence
  UpperCoreExtraction UpperOpenMathCapHeavyTriples UpperOpenMathCoreComponents Finset

theorem component_count_pos {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (G : α → TriangleGeometry)
    (nonempty : (core n L).Nonempty) : 0<coreComponentCount n L G := by
  classical
  obtain ⟨p,hp⟩ := nonempty
  let pp : CoreVertex n L := ⟨p,hp⟩
  let s := (coreGraph n L G).connectedComponentMk pp
  have hpos : 0<(components n L G).card := card_pos.mpr ⟨s,components_mem n L G s⟩
  simpa only [components_card] using hpos

theorem component_count_zero_iff {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (G : α → TriangleGeometry) :
    coreComponentCount n L G=0 ↔ core n L=∅ := by
  classical
  constructor
  · intro hzero
    by_contra hnonempty
    have hpos := component_count_pos n L G (nonempty_iff_ne_empty.mpr hnonempty)
    omega
  · intro hempty
    apply Nat.eq_zero_of_not_pos
    intro hpos
    have hcomp : (components n L G).Nonempty := card_pos.mp (by simpa only [components_card] using hpos)
    obtain ⟨s,hs⟩ := hcomp
    obtain ⟨p,hp⟩ := component_nonempty n L G s
    have hcore := component_subset n L G s hp
    rw [hempty] at hcore
    exact notMem_empty p hcore

theorem certificate_three_core_strict {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (small : (core n L).card≤3) (nonempty : (core n L).Nonempty) :
    let G := fun a => ofPredicate n L (tri a) hL (ht a)
    3*(Fintype.card α : ℤ)+(UpperEdgeInventory.edges n L\usedEdges G).card+1≤(n : ℤ)*(n-2) := by
  have degree := UpperOpenMathCoreDegree.certificate_three_core_degree n L hL tri ht small
  have bound := UpperOpenMathComponentPenalty.certificate_degree_two_component_bound n L hL hn tri hi ht degree
  have hpos := component_count_pos n L (fun a => ofPredicate n L (tri a) hL (ht a)) nonempty
  dsimp only at bound ⊢
  omega

theorem certificate_three_core_perfect_simple {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (small : (core n L).card≤3)
    (perfect : (n : ℤ)*(n-2)=3*Fintype.card α) : NoConcurrent n L := by
  classical
  apply (UpperOpenMathDegreeBudgets.core_empty_iff_simple n L hL).mp
  by_contra hnonempty
  have bound := certificate_three_core_strict n L hL hn tri hi ht small (nonempty_iff_ne_empty.mpr hnonempty)
  dsimp only at bound
  rw [perfect] at bound
  have hu : (0 : ℤ)≤(UpperEdgeInventory.edges n L\usedEdges (fun a => ofPredicate n L (tri a) hL (ht a))).card := by positivity
  omega

theorem certificate_four_triple_strict {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (small : (core n L).card≤4) (triples : ∀ p∈core n L, (supports n L p).card=3)
    (nonempty : (core n L).Nonempty) :
    let G := fun a => ofPredicate n L (tri a) hL (ht a)
    3*(Fintype.card α : ℤ)+(UpperEdgeInventory.edges n L\usedEdges G).card+1≤(n : ℤ)*(n-2) := by
  have degree (p : Point) (hp : p∈core n L) :
      coreDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) p≤3 := by
    have hh := UpperOpenMathCoreDegree.certificate_core_degree_bound n L hL tri ht p hp
    change coreDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) p≤(core n L).card-1 at hh
    omega
  have bound := UpperOpenMathTripleDegreeThree.certificate_degree_three_component_bound n L hL hn tri hi ht triples degree
  have hpos := component_count_pos n L (fun a => ofPredicate n L (tri a) hL (ht a)) nonempty
  dsimp only at bound ⊢
  omega

theorem certificate_four_triple_perfect_simple {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (small : (core n L).card≤4) (triples : ∀ p∈core n L, (supports n L p).card=3)
    (perfect : (n : ℤ)*(n-2)=3*Fintype.card α) : NoConcurrent n L := by
  classical
  apply (UpperOpenMathDegreeBudgets.core_empty_iff_simple n L hL).mp
  by_contra hnonempty
  have bound := certificate_four_triple_strict n L hL hn tri hi ht small triples (nonempty_iff_ne_empty.mpr hnonempty)
  dsimp only at bound
  rw [perfect] at bound
  have hu : (0 : ℤ)≤(UpperEdgeInventory.edges n L\usedEdges (fun a => ofPredicate n L (tri a) hL (ht a))).card := by positivity
  omega

#print axioms component_count_zero_iff
theorem certificate_four_core_strict {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (small : (core n L).card≤4) (nonempty : (core n L).Nonempty) :
    let G := fun a => ofPredicate n L (tri a) hL (ht a)
    3*(Fintype.card α : ℤ)+(UpperEdgeInventory.edges n L\usedEdges G).card+1+
      UpperOpenMathMixedDegreeThree.higherSurplus n L≤(n : ℤ)*(n-2) := by
  have degree (p : Point) (hp : p∈core n L) :
      coreDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) p≤3 := by
    have hh := UpperOpenMathCoreDegree.certificate_core_degree_bound n L hL tri ht p hp
    change coreDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) p≤(core n L).card-1 at hh
    omega
  have bound := UpperOpenMathMixedDegreeThree.certificate_mixed_degree_three_component_bound
    n L hL hn tri hi ht degree
  have hpos := component_count_pos n L (fun a => ofPredicate n L (tri a) hL (ht a)) nonempty
  dsimp only at bound ⊢
  omega

theorem higher_surplus_nonnegative (n : ℕ) (L : ℕ → Line ℝ) :
    0≤UpperOpenMathMixedDegreeThree.higherSurplus n L := by
  classical
  unfold UpperOpenMathMixedDegreeThree.higherSurplus
  apply sum_nonneg
  intro p hp
  have hr : (4 : ℤ)≤(supports n L p).card := by exact_mod_cast (mem_filter.mp hp).2
  exact mul_nonneg (by omega) (by omega)

theorem certificate_four_core_perfect_simple {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (small : (core n L).card≤4)
    (perfect : (n : ℤ)*(n-2)=3*Fintype.card α) : NoConcurrent n L := by
  classical
  apply (UpperOpenMathDegreeBudgets.core_empty_iff_simple n L hL).mp
  by_contra hnonempty
  have bound := certificate_four_core_strict n L hL hn tri hi ht small (nonempty_iff_ne_empty.mpr hnonempty)
  dsimp only at bound
  rw [perfect] at bound
  have hu : (0 : ℤ)≤(UpperEdgeInventory.edges n L\usedEdges (fun a => ofPredicate n L (tri a) hL (ht a))).card := by positivity
  have hs := higher_surplus_nonnegative n L
  omega

#print axioms certificate_four_core_strict
#print axioms certificate_four_core_perfect_simple
#print axioms certificate_three_core_strict
#print axioms certificate_three_core_perfect_simple
#print axioms certificate_four_triple_strict
#print axioms certificate_four_triple_perfect_simple
end Kobon.UpperOpenMathSmallCoreRigidity
