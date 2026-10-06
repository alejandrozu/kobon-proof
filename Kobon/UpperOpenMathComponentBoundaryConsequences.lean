import Kobon.UpperOpenMathComponentBoundary

/-! Component-sensitive resource and deficit consequences for arbitrary
real arrangements and any selected triangle certificate family. -/
namespace Kobon.UpperOpenMathComponentBoundaryConsequences
open Cells FanGeometry UpperVertexBudget UpperTriangleIncidence UpperSharedIncidence
  UpperCoreExtraction UpperOpenMathCapHeavyTriples UpperOpenMathCoreComponents
  UpperOpenMathComponentBoundary UpperOpenMathRayResources Finset
open scoped BigOperators

theorem certificate_component_minimum_resources {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a)) :
    let G := fun a => ofPredicate n L (tri a) hL (ht a)
    2*componentBoundaryMinimum n L G≤
      UpperOpenMathCoreCapacity.nonsharedCoreIncidences n L G+coreEndRays n L := by
  have geometric := certificate_component_boundary_resources n L hL hn tri hi ht
  have monotone := Nat.mul_le_mul_left 2 (component_boundary_minimum_le n L
    (fun a => ofPredicate n L (tri a) hL (ht a)))
  exact monotone.trans geometric

theorem certificate_component_count_resources {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a)) :
    let G := fun a => ofPredicate n L (tri a) hL (ht a)
    2*coreComponentCount n L G≤
      UpperOpenMathCoreCapacity.nonsharedCoreIncidences n L G+coreEndRays n L := by
  have bound := certificate_component_minimum_resources n L hL hn tri hi ht
  have monotone := Nat.mul_le_mul_left 2 (components_le_boundary_minimum n L
    (fun a => ofPredicate n L (tri a) hL (ht a)))
  exact monotone.trans bound

theorem certificate_component_boundary_deficit {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a)) :
    let G := fun a => ofPredicate n L (tri a) hL (ht a)
    2*(∑ p∈core n L, (supports n L p).card*((supports n L p).card-3 : ℤ))+
      2*(UpperEdgeInventory.edges n L\usedEdges G).card+2*componentBoundaryCount n L G≤
        2*((n : ℤ)*(n-2)-3*Fintype.card α)+(oneCoreEdges n L G).card := by
  have identity := certificate_defect_ray_identity n L hL hn tri hi ht
  have resources := certificate_component_boundary_resources n L hL hn tri hi ht
  dsimp only at identity resources ⊢
  have resourcesZ : 2*(componentBoundaryCount n L
      (fun a => ofPredicate n L (tri a) hL (ht a)) : ℤ)≤
      UpperOpenMathCoreCapacity.nonsharedCoreIncidences n L
        (fun a => ofPredicate n L (tri a) hL (ht a))+coreEndRays n L := by exact_mod_cast resources
  linarith

#print axioms certificate_component_minimum_resources
#print axioms certificate_component_count_resources
#print axioms certificate_component_boundary_deficit
end Kobon.UpperOpenMathComponentBoundaryConsequences
