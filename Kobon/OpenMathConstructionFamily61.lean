import Kobon.OpenMathConstructionSeed61Visible
import Kobon.BBLEvenInfinite
import Kobon.BBLDeficitTransport
import Kobon.Universal
import Kobon.UpperEvenSimpleOptimality

/-! A new constant-deficit dyadic orbit from an actual compatible61-line
seed. The point count61:1190 is credited to Rohith Poola. Independently
refitting reciprocal slopes supplies a whole true-tangent epsilon interval;
this is what lets the already proved BBL geometry iterate indefinitely.
The admissible epsilon interval may shrink with the depth. -/
namespace Kobon.OpenMathConstructionFamily61
open BBLInfinite BBLEvenInfinite
set_option autoImplicit false
set_option maxHeartbeats 1000000

def q (t : Nat) : Nat := 60*2^t

def oddCount (t : Nat) : Nat := 1200*4^t-10

def evenCount (t : Nat) : Nat := 1200*4^t+30*2^t-12

theorem uniform_seed : UniformSeed 15 1190 := by
  refine ⟨1/100000000,by norm_num,?_⟩
  intro ε he hu
  exact OpenMathConstructionSeed61Normalized.compatible ε he hu.le

theorem uniform_visible_seed : UniformVisibleSeed 15 1190 28
    OpenMathConstructionSeed61Visible.normal := by
  refine ⟨1/100000000,by norm_num,?_⟩
  intro ε he hu
  exact OpenMathConstructionSeed61Visible.compatible ε he hu.le

theorem power_identity (t : Nat) : (2^t)^2=4^t := by
  rw [← pow_mul,Nat.mul_comm t 2,pow_mul]
  norm_num

theorem q_positive (t : Nat) : 60≤q t := by
  have h := Nat.one_le_pow t 2 (by decide)
  dsimp [q]
  omega

theorem q_square (t : Nat) : (q t)^2=3600*4^t := by
  have hh := power_identity t
  unfold q
  nlinarith

theorem q_divisibility (t : Nat) : q t%2=0 ∧ q t%3=0 := by
  unfold q
  simp [Nat.mul_mod]

theorem count_formula (t : Nat) : triangleCount 15 1190 t=oddCount t := by
  have hh := triangleCount_identity 15 1190 t
  have hs : (4*15*2^t)^2=3600*4^t := q_square t
  rw [hs] at hh
  norm_num at hh
  unfold oddCount
  omega

theorem visible_formula (t : Nat) : visibleCount 15 28 t=30*2^t-2 := by
  have hh := visibleCount_identity 15 28 t
  norm_num at hh
  omega

theorem even_formula (t : Nat) :
    triangleCount 15 1190 t+visibleCount 15 28 t=evenCount t := by
  rw [count_formula,visible_formula]
  have hp := Nat.one_le_pow t 4 (by decide)
  have hq := Nat.one_le_pow t 2 (by decide)
  unfold oddCount evenCount
  omega

theorem odd_family (t : Nat) : SimpleLowerBound (q t+1) (oddCount t) := by
  have hh := infinite_family 15 1190 (by decide) uniform_seed t
  simpa only [q,count_formula,show 4*15=60 by decide] using hh

theorem even_family (t : Nat) : SimpleLowerBound (q t+2) (evenCount t) := by
  have hh := infinite_even_family 15 1190 28 (by decide)
    OpenMathConstructionSeed61Visible.normal
    (by norm_num [OpenMathConstructionSeed61Visible.normal,HybridBoundary.normalLine])
    uniform_visible_seed t
  simpa only [q,even_formula,show 4*15=60 by decide] using hh

theorem odd_count_identity (t : Nat) : 3*oddCount t+30=(q t)^2 := by
  have hh := triangleCount_identity 15 1190 t
  have hs : (4*15*2^t)^2=(q t)^2 := by rfl
  rw [hs,count_formula] at hh
  norm_num at hh
  omega

theorem odd_polynomial_gap (t : Nat) :
    (q t+1)*(q t+1-2)/3=oddCount t+9 := by
  have hp := q_positive t
  have hc := odd_count_identity t
  have hs : q t+1-2+1=q t := by omega
  have he : (q t+1)*(q t+1-2)+1=(q t)^2 := by nlinarith
  omega

theorem even_polynomial_gap (t : Nat) :
    (q t+2)*(2*(q t+2)-5)/6=evenCount t+11 := by
  have hc := BBLDeficitTransport.even_constant_gap 15 1190 28 t
    (by decide) (by norm_num [BBLDeficitTransport.oddBenchmark,BBLDeficitTransport.gridOrder])
    (by decide)
  norm_num [BBLDeficitTransport.oddBenchmark,BBLDeficitTransport.gridOrder] at hc
  rw [even_formula] at hc
  have hf := BBLDeficitTransport.evenBenchmark_floor 15 t (by decide)
  rw [hf] at hc
  simpa only [BBLDeficitTransport.gridOrder,q,show 4*15=60 by decide] using hc.symm
theorem odd_baseline_gain (t : Nat) :
    oddCount t=Universal.baseline (q t+1)+(q t/3-11) := by
  have hp := q_positive t
  have hc := odd_count_identity t
  have hq := q_divisibility t
  rw [Universal.baseline_formula (q t+1) (by omega)]
  have hs : (q t+1)%2=1 := by omega
  rw [hs]
  have hl : q t+1-3+2=q t := by omega
  have he : (q t+1)*(q t+1-3)+q t+2=(q t)^2 := by nlinarith
  omega

theorem even_baseline_gain (t : Nat) (ht : 1≤t) :
    evenCount t=Universal.baseline (q t+2)+(q t/6-12) := by
  have hq := q_divisibility t
  have hq6 : q t%6=0 := by omega
  have hs6 : (q t)^2%6=0 := by simp [pow_two,Nat.mul_mod,hq6]
  have hc := even_polynomial_gap t
  have hp := q_positive t
  rw [Universal.baseline_formula (q t+2) (by omega)]
  have hs : (q t+2)%2=0 := by omega
  rw [hs]
  have hpow : 2≤2^t := by
    have hh := Nat.pow_le_pow_right (by decide : 1≤2) ht
    norm_num at hh
    exact hh
  have hbig : 120≤q t := by unfold q; omega
  have hl : q t+2-3+1=q t := by omega
  have he : (q t+2)*(q t+2-3)+2=(q t)^2+q t := by nlinarith
  have he2 : 2*(q t+2)-5+1=2*q t := by omega
  have he3 : (q t+2)*(2*(q t+2)-5)+2=2*(q t)^2+3*q t := by nlinarith
  omega

theorem odd_window (t : Nat) :
    SimpleLowerBound (q t+1) (oddCount t) ∧
    ∀ T, SimpleLowerBound (q t+1) T → T≤oddCount t+9 := by
  refine ⟨odd_family t,?_⟩
  intro T h
  have hp := q_positive t
  have hh := UpperSimpleOptimality.simple_lower_bound_floor (q t+1) T (by omega) h
  simpa only [odd_polynomial_gap] using hh

theorem even_window (t : Nat) :
    SimpleLowerBound (q t+2) (evenCount t) ∧
    ∀ T, SimpleLowerBound (q t+2) T → T≤evenCount t+11 := by
  refine ⟨even_family t,?_⟩
  intro T h
  have hp := q_positive t
  have hq := q_divisibility t
  have heven : (q t+2)%2=0 := by omega
  have hh := UpperEvenSimpleOptimality.simple_lower_bound_even_floor (q t+2) T
    (by omega) heven h
  simpa only [even_polynomial_gap] using hh

#print axioms uniform_seed
#print axioms odd_family
#print axioms even_family
#print axioms odd_window
#print axioms even_window
end Kobon.OpenMathConstructionFamily61

