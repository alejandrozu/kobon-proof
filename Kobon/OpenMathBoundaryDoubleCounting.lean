import Kobon.OpenMathBoundaryRootOrder
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-! Finite double counting of boundary selection across projective normal
sectors. The hypotheses count each actual boundary vertex's choices; no
geometric direction or unverified selection oracle is supplied here.
-/
namespace Kobon.OpenMathBoundaryDoubleCounting
open scoped BigOperators
set_option autoImplicit false

noncomputable def selectedCount {α β : Type*} [Fintype β]
    (p : α → β → Prop) (a : α) : Nat := by
  classical
  exact (Finset.univ.filter (p a)).card

def jointPositive {κ β : Type*} (f g : κ → β → ℝ)
    (a : κ × Bool) (b : β) : Prop :=
  0<Kobon.OpenMathBoundarySectors.signedValue a.2 (f a.1 b) ∧
  0<Kobon.OpenMathBoundarySectors.signedValue a.2 (g a.1 b)

theorem jointPositive_degree {κ β : Type*} [Fintype κ]
    (f g : κ → β → ℝ) (b : β) :
    selectedCount (fun b a => jointPositive f g a b) b=
      ∑ k, Kobon.OpenMathBoundarySectors.choiceCount (f k b) (g k b) := by
  classical
  unfold selectedCount
  rw [Finset.card_filter,Fintype.sum_prod_type]
  unfold Kobon.OpenMathBoundarySectors.choiceCount Kobon.OpenMathBoundarySectors.choices
  simp_rw [Finset.card_filter]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro s _
  by_cases h : 0<Kobon.OpenMathBoundarySectors.signedValue s (f k b) ∧
      0<Kobon.OpenMathBoundarySectors.signedValue s (g k b)
  · simp [jointPositive,h]
  · simp [jointPositive,h]

theorem sum_selectedCount_eq {α β : Type*} [Fintype α] [Fintype β]
    (p : α → β → Prop) (k : Nat)
    (h : ∀ b, selectedCount (fun b a => p a b) b=k) :
    (∑ a, selectedCount p a)=k*Fintype.card β := by
  classical
  unfold selectedCount at h ⊢
  simp only [Finset.card_filter] at h ⊢
  rw [Finset.sum_comm]
  simp_rw [h]
  simp [Nat.mul_comm]

/-- `2*n` actual direction representatives, each boundary vertex selecting
`n-1` of them, force the half-order exterior gain when `n` is odd and the
number of boundary vertices is at least `n-2`. -/
theorem exists_half_gain_of_degree {α β : Type*} [Fintype α] [Fintype β]
    (m : Nat) (hm : 1 ≤ m) (hc : Fintype.card α=4*m+2)
    (hb : 2*m-1 ≤ Fintype.card β) (p : α → β → Prop)
    (h : ∀ b, selectedCount (fun b a => p a b) b=2*m) :
    ∃ a, m ≤ selectedCount p a := by
  apply Kobon.OpenMathBoundaryRootOrder.exists_half_gain m hm hc (selectedCount p)
  rw [sum_selectedCount_eq p (2*m) h]
  exact Nat.mul_le_mul_left (2*m) hb

theorem exists_half_gain_of_choiceCount {β : Type*} [Fintype β]
    (m : Nat) (hm : 1 ≤ m) (hb : 2*m-1 ≤ Fintype.card β)
    (f g : Fin (2*m+1) → β → ℝ)
    (h : ∀ b, (∑ k, Kobon.OpenMathBoundarySectors.choiceCount (f k b) (g k b))=2*m) :
    ∃ a : Fin (2*m+1) × Bool, m ≤ selectedCount (jointPositive f g) a := by
  have hc : Fintype.card (Fin (2*m+1) × Bool)=4*m+2 := by
    simp
    omega
  apply exists_half_gain_of_degree m hm hc hb (jointPositive f g)
  intro b
  rw [jointPositive_degree]
  exact h b

#print axioms sum_selectedCount_eq
#print axioms exists_half_gain_of_degree
#print axioms exists_half_gain_of_choiceCount
end Kobon.OpenMathBoundaryDoubleCounting
