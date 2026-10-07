import Kobon.UpperOpenMathTwoTwoCore
import Kobon.UpperOpenMathComponentRigidity

/-!
# One unit of exact triangle defect per actual shared-core component

When every multiple vertex is incident to at most two shared core sides,
each nonempty connected component has strictly positive local defect cost.
The components are the quotient of the actual finite geometric graph; their
partition and edge counts are extracted, not supplied. Consequently
`3*T + U + c <= n*(n-2)` for every n, where c is their number.
-/
namespace Kobon.UpperOpenMathComponentPenalty
open Cells FanGeometry UpperVertexBudget UpperTriangleIncidence UpperSharedIncidence
  UpperCoreExtraction UpperOpenMathCapHeavyTriples UpperOpenMathCoreComponents Finset
open scoped BigOperators

theorem certificate_closed_component_cost_pos {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (P : Finset Point) (sub : P⊆core n L) (nonempty : P.Nonempty)
    (closed : SharedCoreClosed n L (fun a => ofPredicate n L (tri a) hL (ht a)) P)
    (degree : ∀ p∈P, coreDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) p≤2) :
    1≤componentCost n L (fun a => ofPredicate n L (tri a) hL (ht a)) P := by
  classical
  let G := fun a => ofPredicate n L (tri a) hL (ht a)
  let r := fun p => (supports n L p).card
  let a := ordinaryDegree n L G
  let d := coreDegree n L G
  let e := (componentEdges n L G P).card
  have hr (p : Point) (hp : p∈P) : 3≤r p := core_multiplicity n L hL (sub hp)
  have h1 (p : Point) (hp : p∈P) : a p≤2*r p-4 :=
    UpperOpenMathDegreeBudgets.certificate_local_degree_two n L hL hn tri hi ht p (sub hp) (degree p hp)
  have h2 : ∀ p∈P, d p≤2 := degree
  have hsum : (∑ p∈P, (d p : ℤ))=2*(e : ℤ) := by
    exact_mod_cast closed_degree_sum n L G P closed
  have nonneg := UpperOpenMathComponentRigidity.finite_component_cost_nonnegative P r a d e hr h1 h2 hsum
  have nozero : componentCost n L G P≠0 := by
    intro hz
    have rigid := UpperOpenMathComponentRigidity.finite_component_rigidity P r a d e hr h1 h2 hsum hz
    exact UpperOpenMathTwoTwoCore.certificate_closed_two_two_impossible n L hL hn tri hi ht P sub nonempty closed rigid
  change 0≤componentCost n L G P at nonneg
  change 1≤componentCost n L G P
  omega

theorem certificate_degree_two_component_bound {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (degree : ∀ p∈core n L, coreDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) p≤2) :
    let G := fun a => ofPredicate n L (tri a) hL (ht a)
    3*(Fintype.card α : ℤ)+(UpperEdgeInventory.edges n L\usedEdges G).card+
      coreComponentCount n L G≤(n : ℤ)*(n-2) := by
  classical
  let G := fun a => ofPredicate n L (tri a) hL (ht a)
  have hEach (s : (coreGraph n L G).ConnectedComponent) (hs : s∈components n L G) :
      (1 : ℤ)≤componentCost n L G (componentVertices n L G s) :=
    certificate_closed_component_cost_pos n L hL hn tri hi ht (componentVertices n L G s)
      (component_subset n L G s) (component_nonempty n L G s)
      (component_closed n L hL tri ht s)
      (fun p hp => degree p (component_subset n L G s hp))
  have hSum := sum_le_sum hEach
  simp only [sum_const,nsmul_eq_mul,mul_one,components_card] at hSum
  have hid := certificate_component_cost_identity n L hL hn tri hi ht
  dsimp only at hid
  change 3*(Fintype.card α : ℤ)+(UpperEdgeInventory.edges n L\usedEdges G).card+
    coreComponentCount n L G≤(n : ℤ)*(n-2)
  linarith

#print axioms certificate_closed_component_cost_pos
#print axioms certificate_degree_two_component_bound
end Kobon.UpperOpenMathComponentPenalty
