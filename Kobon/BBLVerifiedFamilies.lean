import Kobon.BBLInfinite
import Kobon.BBLSeed21Normalized
import Kobon.BBLEvenInfinite
import Kobon.BBLSeed21Visible

/-! The unconditional geometric infinite family from the actual parametric
21-line seed. Its trust base includes the existing finite native certificate
checks in BBLSeed21; all recursive geometry is kernel checked. -/
namespace Kobon.BBLVerifiedFamilies
open BBLInfinite BBLRecursiveSeed

theorem seed21_uniform : UniformSeed 5 132 := by
  refine ⟨1/100000,by norm_num,?_⟩
  intro ε he hu
  exact BBLSeed21Normalized.compatible ε he (le_of_lt hu)

/-- Actual simple real straight-line arrangements at every dyadic level. -/
theorem odd_family (t : Nat) :
    SimpleLowerBound (20*2^t+1) ((400*4^t-4)/3) := by
  have hh := infinite_family 5 132 (by decide) seed21_uniform t
  simpa only [seed132_formula,show 4*5=20 by decide] using hh

/-- Including the original 11-line seed gives the customary family indexing. -/
theorem eleven_odd_family (t : Nat) :
    SimpleLowerBound (10*2^t+1) ((100*4^t-4)/3) := by
  cases t with
  | zero =>
    norm_num
    exact SeedFamily.simple_lower_bound (1/100000) (by norm_num) (by norm_num)
  | succ t =>
    have hn : 10*2^(t+1)+1=20*2^t+1 := by rw [pow_succ]; ring
    have ht : 100*4^(t+1)=400*4^t := by rw [pow_succ]; ring
    simpa only [hn,ht] using odd_family t

theorem seed21_visible_uniform : BBLEvenInfinite.UniformVisibleSeed 5 132 10
    BBLSeed21Visible.normal := by
  refine ⟨1/100000,by norm_num,?_⟩
  intro ε he hu
  exact BBLSeed21Visible.compatible ε he (le_of_lt hu)

/-- The full q/2 exterior gain is realized at every dyadic level. -/
theorem even_family (t : Nat) :
    SimpleLowerBound (20*2^t+2) ((400*4^t-4)/3+10*2^t) := by
  have hh := BBLEvenInfinite.infinite_even_family 5 132 10 (by decide) BBLSeed21Visible.normal
    (by norm_num [BBLSeed21Visible.normal,HybridBoundary.normalLine]) seed21_visible_uniform t
  have hv : BBLEvenInfinite.visibleCount 5 10 t=10*2^t :=
    BBLEvenInfinite.visibleCount_full 5 t
  simpa only [seed132_formula,hv,show 4*5=20 by decide] using hh

/-- Including the original five-wedge seed gives both parities from 11 onward. -/
theorem eleven_even_family (t : Nat) :
    SimpleLowerBound (10*2^t+2) ((100*4^t-4)/3+5*2^t) := by
  cases t with
  | zero =>
    norm_num
    exact HybridBoundary.seed_exterior (1/100000) (by norm_num) (by norm_num)
  | succ t =>
    have hn : 10*2^(t+1)+2=20*2^t+2 := by rw [pow_succ]; ring
    have ht : 100*4^(t+1)=400*4^t := by rw [pow_succ]; ring
    have hv : 5*2^(t+1)=10*2^t := by rw [pow_succ]; ring
    simpa only [hn,ht,hv] using even_family t

#print axioms seed21_uniform
#print axioms odd_family
#print axioms eleven_odd_family
#print axioms even_family
#print axioms eleven_even_family
end Kobon.BBLVerifiedFamilies
