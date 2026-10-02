import Kobon.UpperCoreExtraction
import Kobon.CleanLineBudget
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Extracted finite core-edge counts and multiplicity surplus

Core-to-core shared edges are actual two-element subsets of the finite core,
so their total is at most `choose(q,2)`. The multiplicity surplus used in the
upper-budget arithmetic is also summed over the actual core points here.
-/
namespace Kobon.UpperCoreCombinatorics
open Cells FanGeometry UpperVertexBudget UpperTriangleIncidence
  UpperSharedIncidence UpperEdgeInventory UpperCoreExtraction Finset
open scoped BigOperators

theorem core_edge_subset {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L)
    (tri : α → Triple) (ht : ∀ a, TrianglePredicate n L (tri a)) :
    let geometry := fun a => ofPredicate n L (tri a) hL (ht a)
    twoCoreEdges n L geometry⊆(core n L).powersetCard 2 := by
  classical
  dsimp only
  intro e he
  have hused := (mem_filter.mp (mem_sdiff.mp he).1).1
  apply mem_powersetCard.mpr
  refine ⟨?_,used_edge_card _ hused⟩
  intro p hp
  exact mem_filter.mpr ⟨certificate_side_vertices n L hL tri ht hused hp,
    twoCore_endpoints n L _ he p hp⟩

/-- The actual shared-core graph is simple, expressed without assuming a
graph interface: each edge is a distinct unordered pair of actual core points. -/
theorem core_edge_count {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L)
    (tri : α → Triple) (ht : ∀ a, TrianglePredicate n L (tri a)) :
    let geometry := fun a => ofPredicate n L (tri a) hL (ht a)
    (twoCoreEdges n L geometry).card≤(core n L).card.choose 2 := by
  have hh := card_le_card (core_edge_subset n L hL tri ht)
  simpa only [card_powersetCard] using hh

theorem three_core_edge_count {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L)
    (tri : α → Triple) (ht : ∀ a, TrianglePredicate n L (tri a))
    (hcore : (core n L).card≤3) :
    let geometry := fun a => ofPredicate n L (tri a) hL (ht a)
    (twoCoreEdges n L geometry).card≤3 := by
  have hh := core_edge_count n L hL tri ht
  have hc := Nat.choose_le_choose 2 hcore
  norm_num at hc
  omega

/-- The exact multiplicity surplus is nonnegative because every extracted
core point has multiplicity at least three. -/
theorem core_surplus (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) :
    0≤2*(∑ p∈core n L, (supports n L p).card*((supports n L p).card-2 : ℤ))-
      7*(∑ p∈core n L, ((supports n L p).card : ℤ))+15*(core n L).card := by
  classical
  have hpoint (p : Point) (hp : p∈core n L) :
      0≤2*((supports n L p).card : ℤ)*((supports n L p).card-2)-
        7*(supports n L p).card+15 := by
    simpa only [mul_assoc] using CleanLineBudget.multiplicity_surplus ((supports n L p).card : ℤ)
      (by exact_mod_cast core_multiplicity n L hL hp)
  have hh := sum_nonneg hpoint
  simp only [sum_add_distrib,sum_sub_distrib,← mul_sum,sum_const,nsmul_eq_mul] at hh
  have hmul : (∑ p∈core n L, 2*((supports n L p).card : ℤ)*((supports n L p).card-2))=
      2*(∑ p∈core n L, (supports n L p).card*((supports n L p).card-2 : ℤ)) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro p _
    ring
  rw [hmul] at hh
  nlinarith

#print axioms core_edge_count
#print axioms three_core_edge_count
#print axioms core_surplus
end Kobon.UpperCoreCombinatorics


