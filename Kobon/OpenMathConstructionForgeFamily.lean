import Kobon.OpenMathConstructionSeed33Visible
import Kobon.BBLForgeConditional
import Kobon.UpperEvenSimpleOptimality

/-! Unconditional geometric completion of the classical Forge--Ramirez Alfonsin
odd family and its full simple-even companions. The finite actual tangent-grid
seed, sorted-grid invariant and visible boundary have all been supplied.
The numerical formulas and original doubling construction retain their
historical attribution. -/
namespace Kobon.OpenMathConstructionForgeFamily
open BBLInfinite BBLEvenInfinite BBLForgeConditional
set_option autoImplicit false

theorem uniform_seed : UniformSeed 8 341 := by
  refine ⟨1/100000,by norm_num,?_⟩
  intro ε he hu
  exact OpenMathConstructionSeed33Normalized.compatible ε he hu.le

theorem uniform_visible_seed : UniformVisibleSeed 8 341 16
    OpenMathConstructionSeed33Visible.normal := by
  refine ⟨1/100000,by norm_num,?_⟩
  intro ε he hu
  exact OpenMathConstructionSeed33Visible.compatible ε he hu.le

theorem odd_family (t : Nat) : SimpleLowerBound (q t+1) (oddCount t) :=
  BBLForgeConditional.odd_family uniform_seed t

theorem even_family (t : Nat) : SimpleLowerBound (q t+2) (evenCount t) :=
  BBLForgeConditional.even_family OpenMathConstructionSeed33Visible.normal
    (by norm_num [OpenMathConstructionSeed33Visible.normal,HybridBoundary.normalLine])
    uniform_visible_seed t

theorem odd_optimal_in_simple_arrangements (t : Nat) :
    SimpleLowerBound (q t+1) (oddCount t) ∧
    ∀ T : Nat, SimpleLowerBound (q t+1) T → T≤oddCount t := by
  refine ⟨odd_family t,?_⟩
  intro T h
  have hp := q_properties t
  have hu := UpperSimpleOptimality.simple_lower_bound_floor (q t+1) T (by omega) h
  simpa only [odd_polynomial_exact] using hu

theorem even_optimal_in_simple_arrangements (t : Nat) :
    SimpleLowerBound (q t+2) (evenCount t) ∧
    ∀ T : Nat, SimpleLowerBound (q t+2) T → T≤evenCount t := by
  refine ⟨even_family t,?_⟩
  intro T h
  have hp := q_properties t
  have heven : (q t+2)%2=0 := by omega
  have hu := UpperEvenSimpleOptimality.simple_lower_bound_even_floor (q t+2) T
    (by omega) heven h
  simpa only [even_simple_polynomial_exact] using hu

#print axioms uniform_seed
#print axioms odd_family
#print axioms even_family
#print axioms odd_optimal_in_simple_arrangements
#print axioms even_optimal_in_simple_arrangements
end Kobon.OpenMathConstructionForgeFamily