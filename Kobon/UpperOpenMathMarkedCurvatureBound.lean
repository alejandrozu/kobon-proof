import Kobon.UpperOpenMathMarkedCurvature
import Kobon.UpperOpenMathMarkedZeroEscape

/-!
# Unrestricted triple-core component curvature with reduced exceptions

Only unmarked full two-cap fans and full one-cap fans remain as negative
corrections. Every nonempty actual shared-core component has positive cost
after these corrections, with no maximum-degree hypothesis.
-/
namespace Kobon.UpperOpenMathMarkedCurvatureBound
open Cells FanGeometry UpperVertexBudget UpperTriangleIncidence UpperSharedIncidence
  UpperCoreExtraction UpperOpenMathCapHeavyTriples UpperOpenMathCoreComponents
  UpperOpenMathMarkedPorts UpperOpenMathMarkedCurvature Finset
open scoped BigOperators

theorem certificate_closed_marked_cost_pos {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (triples : ∀ p∈core n L, (supports n L p).card=3)
    (P : Finset Point) (sub : P⊆core n L) (nonempty : P.Nonempty)
    (closed : SharedCoreClosed n L (fun a => ofPredicate n L (tri a) hL (ht a)) P) :
    1≤componentCost n L (fun a => ofPredicate n L (tri a) hL (ht a)) P+
      unpaidOn n L hL hn tri ht P := by
  classical
  let G := fun a => ofPredicate n L (tri a) hL (ht a)
  have data := certificate_closed_marked_data n L hL hn tri hi ht triples P sub closed
  have nonnegative := unpaidOn_nonnegative n L hL hn tri ht P
  change 0≤2*componentCost n L G P+unpaidOn n L hL hn tri ht P ∧ _ at data
  change 1≤componentCost n L G P+unpaidOn n L hL hn tri ht P
  by_cases unpaidZero : unpaidOn n L hL hn tri ht P=0
  · have nozero : componentCost n L G P≠0 := by
      intro costZero
      obtain ⟨tight,types⟩ := data.2 unpaidZero costZero
      exact UpperOpenMathMarkedZeroEscape.closed_marked_zero_impossible
        n L hL hn tri hi ht triples P sub nonempty closed tight types
    omega
  · omega

theorem component_unpaid_sum {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (ht : ∀ a, TrianglePredicate n L (tri a)) :
    let G := fun a => ofPredicate n L (tri a) hL (ht a)
    (∑ s∈components n L G, unpaidOn n L hL hn tri ht (componentVertices n L G s))=
      unpaidOn n L hL hn tri ht (core n L) := by
  classical
  dsimp only
  unfold unpaidOn
  exact component_sum n L _ _

theorem certificate_marked_component_bound {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (triples : ∀ p∈core n L, (supports n L p).card=3) :
    let G := fun a => ofPredicate n L (tri a) hL (ht a)
    3*(Fintype.card α : ℤ)+(UpperEdgeInventory.edges n L\usedEdges G).card+coreComponentCount n L G≤
      (n : ℤ)*(n-2)+unpaidOn n L hL hn tri ht (core n L) := by
  classical
  let G := fun a => ofPredicate n L (tri a) hL (ht a)
  have each (s : (coreGraph n L G).ConnectedComponent) (hs : s∈components n L G) :
      (1 : ℤ)≤componentCost n L G (componentVertices n L G s)+
        unpaidOn n L hL hn tri ht (componentVertices n L G s) :=
    certificate_closed_marked_cost_pos n L hL hn tri hi ht triples (componentVertices n L G s)
      (component_subset n L G s) (component_nonempty n L G s) (component_closed n L hL tri ht s)
  have hs := sum_le_sum each
  simp only [sum_add_distrib,sum_const,nsmul_eq_mul,mul_one,components_card] at hs
  have unpaidSum := component_unpaid_sum n L hL hn tri ht
  dsimp only at unpaidSum
  rw [unpaidSum] at hs
  have identity := certificate_component_cost_identity n L hL hn tri hi ht
  dsimp only at identity
  change 3*(Fintype.card α : ℤ)+(UpperEdgeInventory.edges n L\usedEdges G).card+coreComponentCount n L G≤
    (n : ℤ)*(n-2)+unpaidOn n L hL hn tri ht (core n L)
  linarith

theorem certificate_unmarked_exception_bound {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (triples : ∀ p∈core n L, (supports n L p).card=3) :
    let G := fun a => ofPredicate n L (tri a) hL (ht a)
    3*(Fintype.card α : ℤ)+(UpperEdgeInventory.edges n L\usedEdges G).card+coreComponentCount n L G≤
      (n : ℤ)*(n-2)+
      2*((core n L).filter (fun p => ordinaryDegree n L G p=2 ∧ coreDegree n L G p=4 ∧
        markedCount n L hL hn tri ht p=0)).card+
      ((core n L).filter (fun p => ordinaryDegree n L G p=1 ∧ coreDegree n L G p=5)).card := by
  have h := certificate_marked_component_bound n L hL hn tri hi ht triples
  rw [unpaidOn_counts] at h
  dsimp only at h ⊢
  linarith

#print axioms certificate_closed_marked_cost_pos
#print axioms certificate_marked_component_bound
#print axioms certificate_unmarked_exception_bound
end Kobon.UpperOpenMathMarkedCurvatureBound
