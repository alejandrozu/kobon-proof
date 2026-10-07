import Kobon.UpperOpenMathPerfectRigidity
import Kobon.UpperOpenMathCoreComponents

/-! Finite arithmetic for closed components of the actual shared-core
graph. The application supplies the ordinary fan bound and the exact
internal endpoint count from geometric extraction. This helper does not
assert those identities for arbitrary unverified data. -/
namespace Kobon.UpperOpenMathComponentRigidity
open Cells FanGeometry UpperVertexBudget UpperTriangleIncidence
  UpperSharedIncidence UpperCoreExtraction UpperOpenMathCapHeavyTriples
  UpperOpenMathCoreComponents UpperOpenMathDegreeBudgets Finset
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem finite_component_rigidity {β : Type*} (P : Finset β)
    (r d1 d2 : β→Nat) (e : Nat)
    (hr : ∀ p∈P, 3≤r p)
    (h1 : ∀ p∈P, d1 p≤2*r p-4)
    (h2 : ∀ p∈P, d2 p≤2)
    (sumCore : (∑ p∈P, (d2 p : ℤ))=2*(e : ℤ))
    (balanced : (∑ p∈P, (r p : ℤ)*(r p-2))-
      (∑ p∈P, (d1 p : ℤ))-(e : ℤ)=0) :
    ∀ p∈P, r p=3 ∧ d1 p=2 ∧ d2 p=2 := by
  classical
  let weight : β→ℤ := fun p => 2*(r p : ℤ)*(r p-2)-2*d1 p-d2 p
  have hrZ (p : β) (hp : p∈P) : (3 : ℤ)≤r p := by exact_mod_cast hr p hp
  have h1Z (p : β) (hp : p∈P) : (d1 p : ℤ)+4≤2*r p := by
    have hN : d1 p+4≤2*r p := by have := hr p hp; have := h1 p hp; omega
    exact_mod_cast hN
  have h2Z (p : β) (hp : p∈P) : (d2 p : ℤ)≤2 := by exact_mod_cast h2 p hp
  have hnonneg (p : β) (hp : p∈P) : 0≤weight p := by
    have hR := hrZ p hp
    have hD1 := h1Z p hp
    have hD2 := h2Z p hp
    have hh := mul_nonneg (by omega : (0 : ℤ)≤r p-3) (by omega : (0 : ℤ)≤r p-1)
    dsimp [weight]
    nlinarith
  have hfactor : (∑ p∈P, 2*(r p : ℤ)*(r p-2))=
      2*(∑ p∈P, (r p : ℤ)*(r p-2)) := by
    rw [mul_sum]
    exact sum_congr rfl (fun p _ => by ring)
  have htotal : (∑ p∈P, weight p)=0 := by
    simp only [weight,sum_sub_distrib,hfactor,← mul_sum]
    rw [sumCore]
    linarith only [balanced]
  have heach := (sum_eq_zero_iff_of_nonneg hnonneg).mp htotal
  intro p hp
  have hR := hrZ p hp
  have hD1 := h1Z p hp
  have hD2 := h2Z p hp
  have hW := heach p hp
  dsimp [weight] at hW
  have hR3 : (r p : ℤ)=3 := by
    nlinarith [sq_nonneg ((r p : ℤ)-3)]
  have hD12 : (d1 p : ℤ)=2 := by rw [hR3] at hW hD1; omega
  have hD22 : (d2 p : ℤ)=2 := by rw [hR3,hD12] at hW; omega
  exact ⟨by exact_mod_cast hR3,by exact_mod_cast hD12,by exact_mod_cast hD22⟩

theorem finite_component_cost_nonnegative {β : Type*} (P : Finset β)
    (r d1 d2 : β→Nat) (e : Nat)
    (hr : ∀ p∈P, 3≤r p)
    (h1 : ∀ p∈P, d1 p≤2*r p-4)
    (h2 : ∀ p∈P, d2 p≤2)
    (sumCore : (∑ p∈P, (d2 p : ℤ))=2*(e : ℤ)) :
    0≤(∑ p∈P, (r p : ℤ)*(r p-2))-(∑ p∈P, (d1 p : ℤ))-(e : ℤ) := by
  have hp (p : β) (hp : p∈P) :
      2*(d1 p : ℤ)+(d2 p : ℤ)≤2*(r p : ℤ)*(r p-2) := by
    have hR : (3 : ℤ)≤r p := by exact_mod_cast hr p hp
    have hN : d1 p+4≤2*r p := by have := hr p hp; have := h1 p hp; omega
    have hD1 : (d1 p : ℤ)+4≤2*r p := by exact_mod_cast hN
    have hD2 : (d2 p : ℤ)≤2 := by exact_mod_cast h2 p hp
    nlinarith [mul_nonneg (by omega : (0 : ℤ)≤r p-3) (by omega : (0 : ℤ)≤r p-1)]
  have hs := sum_le_sum (s:=P) hp
  have hfactor : (∑ p∈P, 2*(r p : ℤ)*(r p-2))=
      2*(∑ p∈P, (r p : ℤ)*(r p-2)) := by
    rw [mul_sum]
    exact sum_congr rfl (fun p _ => by ring)
  simp only [sum_add_distrib,← mul_sum,hfactor] at hs
  rw [sumCore] at hs
  linarith only [hs]

#print axioms finite_component_rigidity
#print axioms finite_component_cost_nonnegative

theorem certificate_closed_cost_nonnegative {α : Type*} [Fintype α]
    (n : Nat) (L : Nat→Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α→Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (P : Finset Point) (subset : P⊆core n L)
    (closed : SharedCoreClosed n L (fun a => ofPredicate n L (tri a) hL (ht a)) P)
    (degree : ∀ p∈P, coreDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) p≤2) :
    0≤componentCost n L (fun a => ofPredicate n L (tri a) hL (ht a)) P := by
  let G := fun a => ofPredicate n L (tri a) hL (ht a)
  apply finite_component_cost_nonnegative P (fun p => (supports n L p).card)
    (ordinaryDegree n L G) (coreDegree n L G) (componentEdges n L G P).card
  · intro p hp
    exact core_multiplicity n L hL (subset hp)
  · intro p hp
    exact certificate_local_degree_two n L hL hn tri hi ht p (subset hp) (degree p hp)
  · exact degree
  · exact_mod_cast closed_degree_sum n L G P closed

theorem certificate_closed_balanced_rigidity {α : Type*} [Fintype α]
    (n : Nat) (L : Nat→Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α→Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (P : Finset Point) (subset : P⊆core n L)
    (closed : SharedCoreClosed n L (fun a => ofPredicate n L (tri a) hL (ht a)) P)
    (degree : ∀ p∈P, coreDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) p≤2)
    (balanced : componentCost n L (fun a => ofPredicate n L (tri a) hL (ht a)) P=0) :
    let G := fun a => ofPredicate n L (tri a) hL (ht a)
    ∀ p∈P, (supports n L p).card=3 ∧ ordinaryDegree n L G p=2 ∧ coreDegree n L G p=2 := by
  let G := fun a => ofPredicate n L (tri a) hL (ht a)
  apply finite_component_rigidity P (fun p => (supports n L p).card)
    (ordinaryDegree n L G) (coreDegree n L G) (componentEdges n L G P).card
  · intro p hp
    exact core_multiplicity n L hL (subset hp)
  · intro p hp
    exact certificate_local_degree_two n L hL hn tri hi ht p (subset hp) (degree p hp)
  · exact degree
  · exact_mod_cast closed_degree_sum n L G P closed
  · exact balanced

#print axioms certificate_closed_cost_nonnegative
#print axioms certificate_closed_balanced_rigidity
end Kobon.UpperOpenMathComponentRigidity
