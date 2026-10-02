import Kobon.BBLFamilyBenchmarks
import Kobon.UpperEvenSimpleOptimality

/-! Actual one-triangle windows for the verified eleven-seed families.
These are bounds for simple real straight-line arrangements. They make no
claim that unrestricted arrangements with multiple intersections satisfy
the same even upper bound, and do not assert numerical novelty. -/
namespace Kobon.BBLFamilyOptimality

open BBLFamilyBenchmarks

theorem odd_upper (t T : Nat) (h : SimpleLowerBound (q t+1) T) :
    T≤oddCount t+1 := by
  have hq := (q_properties t).1
  have hu := UpperSimpleOptimality.simple_lower_bound_floor
    (q t+1) T (by omega) h
  rw [odd_polynomial_gap] at hu
  exact hu

theorem even_upper (t T : Nat) (h : SimpleLowerBound (q t+2) T) :
    T≤evenCount t+1 := by
  have hq := q_properties t
  have hu := UpperEvenSimpleOptimality.simple_lower_bound_even_floor
    (q t+2) T (by omega) (by omega) h
  rw [even_simple_polynomial_gap] at hu
  exact hu

/-- Existence and a universal upper bound differ by exactly one triangle. -/
theorem odd_window (t : Nat) :
    SimpleLowerBound (q t+1) (oddCount t) ∧
      ∀ T, SimpleLowerBound (q t+1) T → T≤oddCount t+1 :=
  ⟨odd_sound t,odd_upper t⟩

/-- The corresponding actual window for even simple arrangements. -/
theorem even_window (t : Nat) :
    SimpleLowerBound (q t+2) (evenCount t) ∧
      ∀ T, SimpleLowerBound (q t+2) T → T≤evenCount t+1 :=
  ⟨even_sound t,even_upper t⟩

#print axioms odd_upper
#print axioms even_upper
#print axioms odd_window
#print axioms even_window
end Kobon.BBLFamilyOptimality
