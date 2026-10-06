import Kobon.OpenMathConstructionPareto61Visible
import Kobon.OpenMathConstructionFamily61

/-! A stronger even dyadic orbit from the independently certified1190/29
uniform seed. The odd count is retained; the geometric visible resource
improves from28 to29. BBL transport preserves that one-pair improvement
at every depth. Neither61:1190 nor62:1219 is claimed a new finite record.
-/
namespace Kobon.OpenMathConstructionParetoFamily61
open BBLInfinite BBLEvenInfinite
set_option autoImplicit false
set_option maxHeartbeats 1000000

abbrev q := OpenMathConstructionFamily61.q
abbrev oddCount := OpenMathConstructionFamily61.oddCount
def evenCount (t : Nat) : Nat := OpenMathConstructionFamily61.evenCount t+1

theorem uniform_visible_seed : UniformVisibleSeed 15 1190 29
    OpenMathConstructionPareto61Visible.normal := by
  refine ⟨1/100000000,by norm_num,?_⟩
  intro ε he hu
  exact OpenMathConstructionPareto61Visible.compatible ε he hu.le

theorem visible_improvement (t : Nat) :
    visibleCount 15 29 t=visibleCount 15 28 t+1 := by
  have h := visibleCount_identity 15 29 t
  have h' := visibleCount_identity 15 28 t
  omega

theorem visible_formula (t : Nat) : visibleCount 15 29 t=30*2^t-1 := by
  have h := visibleCount_identity 15 29 t
  norm_num at h
  omega

theorem even_formula (t : Nat) :
    triangleCount 15 1190 t+visibleCount 15 29 t=evenCount t := by
  rw [visible_improvement]
  have h := OpenMathConstructionFamily61.even_formula t
  unfold evenCount
  omega

theorem even_polynomial (t : Nat) : evenCount t=1200*4^t+30*2^t-11 := by
  have h := Nat.one_le_pow t 4 (by decide)
  have h' := Nat.one_le_pow t 2 (by decide)
  unfold evenCount OpenMathConstructionFamily61.evenCount
  omega

theorem odd_family (t : Nat) : SimpleLowerBound (q t+1) (oddCount t) :=
  OpenMathConstructionFamily61.odd_family t

theorem even_family (t : Nat) : SimpleLowerBound (q t+2) (evenCount t) := by
  have h := infinite_even_family 15 1190 29 (by decide)
    OpenMathConstructionPareto61Visible.normal
    (by norm_num [OpenMathConstructionPareto61Visible.normal,HybridBoundary.normalLine])
    uniform_visible_seed t
  simpa only [q,OpenMathConstructionFamily61.q,even_formula,show 4*15=60 by decide]
    using h

theorem improves_prior_even_family (t : Nat) :
    SimpleLowerBound (q t+2) (OpenMathConstructionFamily61.evenCount t+1) :=
  even_family t

theorem even_classical (t : Nat) : LowerBound (q t+2) (evenCount t) :=
  (even_family t).classical

theorem even_polynomial_gap (t : Nat) :
    (q t+2)*(2*(q t+2)-5)/6=evenCount t+10 := by
  have h := OpenMathConstructionFamily61.even_polynomial_gap t
  unfold evenCount
  omega

theorem even_baseline_gain (t : Nat) (ht : 1≤t) :
    evenCount t=Universal.baseline (q t+2)+(q t/6-11) := by
  have h := OpenMathConstructionFamily61.even_baseline_gain t ht
  have hpow : 2≤2^t := by
    have hh := Nat.pow_le_pow_right (by decide : 1≤2) ht
    norm_num at hh
    exact hh
  have hq : 120≤q t := by unfold q OpenMathConstructionFamily61.q; omega
  unfold evenCount
  dsimp only [q] at *
  omega

theorem even_window (t : Nat) :
    SimpleLowerBound (q t+2) (evenCount t) ∧
      ∀ T, SimpleLowerBound (q t+2) T → T≤evenCount t+10 := by
  refine ⟨even_family t,?_⟩
  intro T h
  have hp := OpenMathConstructionFamily61.q_positive t
  have hq := OpenMathConstructionFamily61.q_divisibility t
  have heven : (OpenMathConstructionFamily61.q t+2)%2=0 := by omega
  have hh := UpperEvenSimpleOptimality.simple_lower_bound_even_floor (OpenMathConstructionFamily61.q t+2) T
    (by omega) heven h
  have hg : (OpenMathConstructionFamily61.q t+2)*(2*(OpenMathConstructionFamily61.q t+2)-5)/6=evenCount t+10 := even_polynomial_gap t
  rwa [hg] at hh

#print axioms uniform_visible_seed
#print axioms even_family
#print axioms even_classical
#print axioms even_window
end Kobon.OpenMathConstructionParetoFamily61
