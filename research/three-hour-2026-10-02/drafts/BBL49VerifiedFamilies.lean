import Kobon.BBLSeed49Normalized
import Kobon.BBLInfinite
import Kobon.BBLSeed49Visible
import Kobon.BBLEvenInfinite
import Kobon.UpperSimpleOptimality

/-! Actual straight-line dyadic families from the uniform optimal 49-line seed.
The odd orders are the s=t+3 tail of the already known 6*2^s+1 family in
Bartholdi--Blanc--Loisel, arXiv:0706.0723, Theorem 1.3. This module closes a
Lean geometric realization and simple optimality proof, not a new numerical family.
The geometric seed proof retains its explicitly audited native finite checks;
the recursion and closed-form arithmetic introduce no further oracle. -/
namespace Kobon.BBL49VerifiedFamilies
open BBLInfinite
set_option autoImplicit false

theorem seed49_uniform : UniformSeed 12 767 := by
  refine ⟨1/100,by norm_num,?_⟩
  intro ε he hu
  exact BBLSeed49Normalized.compatible ε he (le_of_lt hu)

theorem square_identity (t : Nat) : (48*2^t)^2=2304*4^t := by
  have hp : (2^t)^2=4^t := by
    rw [← pow_mul,Nat.mul_comm t 2,pow_mul]
    norm_num
  nlinarith [hp]

theorem count767_formula (t : Nat) : triangleCount 12 767 t=768*4^t-1 := by
  have h := triangleCount_identity 12 767 t
  norm_num only at h
  rw [square_identity] at h
  omega

/-- Existence at every finite doubling depth, with all seed hypotheses discharged. -/
theorem odd_family (t : Nat) :
    SimpleLowerBound (48*2^t+1) (768*4^t-1) := by
  have h := infinite_family 12 767 (by decide) seed49_uniform t
  simpa only [count767_formula,show 4*12=48 by decide] using h

theorem seed49_visible_uniform : BBLEvenInfinite.UniformVisibleSeed 12 767 24
    BBLSeed49Visible.normal := by
  refine ⟨1/100,by norm_num,?_⟩
  intro ε he hu
  exact BBLSeed49Visible.compatible ε he (le_of_lt hu)

/-- The full half-grid exterior gain is realized at every finite depth. -/
theorem even_family (t : Nat) :
    SimpleLowerBound (48*2^t+2) (768*4^t-1+24*2^t) := by
  have h := BBLEvenInfinite.infinite_even_family 12 767 24 (by decide)
    BBLSeed49Visible.normal (by norm_num [BBLSeed49Visible.normal,HybridBoundary.normalLine])
    seed49_visible_uniform t
  have hv : BBLEvenInfinite.visibleCount 12 24 t=24*2^t :=
    BBLEvenInfinite.visibleCount_full 12 t
  simpa only [count767_formula,hv,show 4*12=48 by decide] using h

/-- Arithmetic comparison to the classical odd polynomial benchmark only. -/
theorem odd_polynomial_exact (t : Nat) :
    (48*2^t+1)*(48*2^t-1)/3=768*4^t-1 := by
  have hp : 1≤2^t := Nat.one_le_pow t 2 (by decide)
  have hq : 1≤48*2^t := by omega
  have hs := square_identity t
  have hmul : (48*2^t+1)*(48*2^t-1)+1=(48*2^t)^2 := by
    nlinarith [Nat.sub_add_cancel hq]
  omega

/-- Arithmetic equality with the sharper even simple-arrangement benchmark. -/
theorem even_polynomial_exact (t : Nat) :
    (48*2^t+2)*(2*(48*2^t+2)-5)/6=768*4^t-1+24*2^t := by
  have hp : 1≤2^t := Nat.one_le_pow t 2 (by decide)
  have hp4 : 1≤4^t := Nat.one_le_pow t 4 (by decide)
  have hq : 1≤96*2^t := by omega
  have hc : 1≤768*4^t := by omega
  have hs := square_identity t
  have hsub : 2*(48*2^t+2)-5=96*2^t-1 := by omega
  rw [hsub]
  have hmul : (48*2^t+2)*(96*2^t-1)+2=4608*4^t+144*2^t := by
    nlinarith [Nat.sub_add_cancel hq]
  omega

/-- Exact optimal count within the simple, pairwise nonparallel model. -/
theorem odd_exact (t T : Nat) :
    SimpleLowerBound (48*2^t+1) T ↔ T≤768*4^t-1 := by
  constructor
  · intro h
    have hp : 1≤2^t := Nat.one_le_pow t 2 (by decide)
    have hu := UpperSimpleOptimality.simple_lower_bound_floor (48*2^t+1) T (by omega) h
    have he : 48*2^t+1-2=48*2^t-1 := by omega
    simpa only [he,odd_polynomial_exact] using hu
  · intro h
    exact (odd_family t).mono h

#print axioms odd_family
#print axioms even_family
#print axioms odd_polynomial_exact
#print axioms even_polynomial_exact
#print axioms odd_exact
end Kobon.BBL49VerifiedFamilies
