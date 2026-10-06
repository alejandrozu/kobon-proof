import Kobon.OpenMathBoundaryDoubleCounting
import Mathlib.Algebra.Order.Floor.Div

/-! Exact integer averaging for arbitrary finite direction sets. This is the
general quantitative arithmetic step; geometric boundary resources and exterior
insertion are supplied separately by their actual witness theorems.
-/
namespace Kobon.OpenMathBoundaryIntegerAveraging
open scoped BigOperators
set_option autoImplicit false

theorem exists_gain_of_sum_threshold {α : Type*} [Fintype α]
    (f : α → Nat) (g : Nat) (hg : 0<g)
    (h : Fintype.card α*(g-1)<∑ a, f a) : ∃ a, g ≤ f a := by
  classical
  by_contra hn
  push Not at hn
  have hb : ∀ a, f a ≤ g-1 := by intro a; have := hn a; omega
  have hu : (∑ a, f a) ≤ Fintype.card α*(g-1) := by
    calc
      _ ≤ ∑ _a : α, (g-1) := Finset.sum_le_sum (fun a _ => hb a)
      _ = _ := by simp
  exact (not_lt_of_ge hu) h

theorem exists_ceiling_of_sum {α : Type*} [Fintype α] [Nonempty α]
    (f : α → Nat) (total : Nat) (h : total ≤ ∑ a, f a) :
    ∃ a, (total+Fintype.card α-1)/Fintype.card α ≤ f a := by
  classical
  obtain ⟨a,_,ha⟩ := Finset.exists_max_image Finset.univ f Finset.univ_nonempty
  have hu : (∑ b, f b) ≤ Fintype.card α*f a := by
    calc
      _ ≤ ∑ _b : α, f a := Finset.sum_le_sum (fun b _ => ha b (Finset.mem_univ b))
      _ = _ := by simp
  refine ⟨a,?_⟩
  rw [←Nat.ceilDiv_eq_add_pred_div]
  exact (ceilDiv_le_iff_le_mul (Fintype.card_pos : 0<Fintype.card α)).mpr (h.trans hu)

theorem exists_ceiling_selected {α β : Type*} [Fintype α] [Nonempty α] [Fintype β]
    (p : α → β → Prop) (k : Nat)
    (h : ∀ b, Kobon.OpenMathBoundaryDoubleCounting.selectedCount (fun b a => p a b) b=k) :
    ∃ a, (k*Fintype.card β+Fintype.card α-1)/Fintype.card α ≤
      Kobon.OpenMathBoundaryDoubleCounting.selectedCount p a := by
  apply exists_ceiling_of_sum
  rw [Kobon.OpenMathBoundaryDoubleCounting.sum_selectedCount_eq p k h]

theorem exists_ceiling_selected_of_card_bound {α β : Type*}
    [Fintype α] [Nonempty α] [Fintype β]
    (p : α → β → Prop) (k B : Nat) (hb : B ≤ Fintype.card β)
    (h : ∀ b, Kobon.OpenMathBoundaryDoubleCounting.selectedCount (fun b a => p a b) b=k) :
    ∃ a, (k*B+Fintype.card α-1)/Fintype.card α ≤
      Kobon.OpenMathBoundaryDoubleCounting.selectedCount p a := by
  apply exists_ceiling_of_sum
  rw [Kobon.OpenMathBoundaryDoubleCounting.sum_selectedCount_eq p k h]
  exact Nat.mul_le_mul_left k hb

#print axioms exists_ceiling_of_sum
#print axioms exists_ceiling_selected_of_card_bound
end Kobon.OpenMathBoundaryIntegerAveraging
