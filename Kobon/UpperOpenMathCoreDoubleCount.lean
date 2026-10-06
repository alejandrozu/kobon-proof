import Kobon.UpperOpenMathCoreCapacity

/-! Double counting for the actual shared side inventory.  A side with one
core endpoint is counted once over the core; a side with two core endpoints
is counted twice.  These identities supply the global sums required when
local cyclic fan inequalities are extracted from real certificate geometry. -/
namespace Kobon.UpperOpenMathCoreDoubleCount
open Cells FanGeometry UpperVertexBudget UpperTriangleIncidence
  UpperSharedIncidence UpperEdgeInventory UpperCoreExtraction
  UpperOpenMathCoreCapacity Finset
open scoped BigOperators
set_option autoImplicit false

theorem endpoint_double_count (P : Finset Point) (E : Finset Edge) :
    (∑ p∈P, (E.filter (fun e => p∈e)).card)=
      ∑ e∈E, (e∩P).card := by
  classical
  have hA (p : Point) : (E.filter (fun e => p∈e)).card=
      ∑ e∈E, if p∈e then 1 else 0 := by simp [sum_boole]
  simp_rw [hA]
  rw [sum_comm]
  apply sum_congr rfl
  intro e he
  have hfilter : P.filter (fun p => p∈e)=e∩P := by
    ext p
    simp only [mem_filter,mem_inter]
    tauto
  simp [Finset.inter_comm]

theorem one_core_incidence_sum {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a)) :
    let geometry := fun a => ofPredicate n L (tri a) hL (ht a)
    (∑ p∈core n L,
      ((oneCoreEdges n L geometry).filter (fun e => p∈e)).card)=
      (oneCoreEdges n L geometry).card := by
  classical
  let geometry := fun a => ofPredicate n L (tri a) hL (ht a)
  change (∑ p∈core n L,
    ((oneCoreEdges n L geometry).filter (fun e => p∈e)).card)=
    (oneCoreEdges n L geometry).card
  rw [endpoint_double_count]
  calc
    _=∑ _e∈oneCoreEdges n L geometry, 1 :=
      sum_congr rfl (fun e he => oneCore_core_card n L hL tri hi ht he)
    _=(oneCoreEdges n L geometry).card := by simp

theorem two_core_incidence_sum {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L)
    (tri : α → Triple) (ht : ∀ a, TrianglePredicate n L (tri a)) :
    let geometry := fun a => ofPredicate n L (tri a) hL (ht a)
    (∑ p∈core n L,
      ((twoCoreEdges n L geometry).filter (fun e => p∈e)).card)=
      2*(twoCoreEdges n L geometry).card := by
  classical
  let geometry := fun a => ofPredicate n L (tri a) hL (ht a)
  change (∑ p∈core n L,
    ((twoCoreEdges n L geometry).filter (fun e => p∈e)).card)=
    2*(twoCoreEdges n L geometry).card
  rw [endpoint_double_count]
  calc
    _=∑ _e∈twoCoreEdges n L geometry, 2 :=
      sum_congr rfl (fun e he => twoCore_core_card n L hL tri ht he)
    _=2*(twoCoreEdges n L geometry).card := by simp [Nat.mul_comm]

#print axioms endpoint_double_count
#print axioms one_core_incidence_sum
#print axioms two_core_incidence_sum
end Kobon.UpperOpenMathCoreDoubleCount
