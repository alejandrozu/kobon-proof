import Kobon.UpperOpenMathComponentHullDeficit

/-! Explicit component-hull penalties for arrangements without low-order
cores. These are structural upper bounds, not an unrestricted numerical
formula for the Kobon maximum. -/
namespace Kobon.UpperOpenMathHighMultiplicityHull
open Cells FanGeometry UpperVertexBudget UpperTriangleIncidence UpperSharedIncidence
  UpperCoreExtraction UpperOpenMathCoreComponents UpperOpenMathComponentBoundary Finset
open scoped BigOperators
set_option maxHeartbeats 1000000

theorem certificate_minimum_multiplicity_hull {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (R : ℕ) (hR : 4≤R) (multiplicity : ∀ p∈core n L, R≤(supports n L p).card) :
    let G := fun a => ofPredicate n L (tri a) hL (ht a)
    6*(Fintype.card α : ℤ)+(2*(R : ℤ)*(R-4)+3)*(core n L).card+
      3*componentBoundaryCount n L G+2*(UpperEdgeInventory.edges n L\usedEdges G).card≤
        2*(n : ℤ)*(n-2) := by
  have lower (p : Point) (hp : p∈core n L) :
      (R : ℤ)*(R-4)≤(supports n L p).card*((supports n L p).card-4 : ℤ) := by
    have rmin : (R : ℤ)≤(supports n L p).card := by exact_mod_cast multiplicity p hp
    have rfour : (4 : ℤ)≤R := by exact_mod_cast hR
    nlinarith
  have total := sum_le_sum lower
  simp only [sum_const,nsmul_eq_mul] at total
  have hull := UpperOpenMathComponentHullDeficit.certificate_component_hull_deficit n L hL hn tri hi ht
  dsimp only at hull ⊢
  nlinarith

theorem certificate_no_triple_hull {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (noTriple : ∀ p∈core n L, (supports n L p).card≠3) :
    let G := fun a => ofPredicate n L (tri a) hL (ht a)
    6*(Fintype.card α : ℤ)+3*(core n L).card+3*componentBoundaryCount n L G+
      2*(UpperEdgeInventory.edges n L\usedEdges G).card≤2*(n : ℤ)*(n-2) := by
  have bound := certificate_minimum_multiplicity_hull n L hL hn tri hi ht 4 (by omega) (by
    intro p hp
    have hr := core_multiplicity n L hL hp
    have hne := noTriple p hp
    omega)
  norm_num at bound
  exact bound

theorem certificate_five_plus_hull {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (multiplicity : ∀ p∈core n L, 5≤(supports n L p).card) :
    let G := fun a => ofPredicate n L (tri a) hL (ht a)
    6*(Fintype.card α : ℤ)+13*(core n L).card+3*componentBoundaryCount n L G+
      2*(UpperEdgeInventory.edges n L\usedEdges G).card≤2*(n : ℤ)*(n-2) := by
  have bound := certificate_minimum_multiplicity_hull n L hL hn tri hi ht 5 (by omega) multiplicity
  norm_num at bound
  exact bound

#print axioms certificate_minimum_multiplicity_hull
#print axioms certificate_no_triple_hull
#print axioms certificate_five_plus_hull
end Kobon.UpperOpenMathHighMultiplicityHull
