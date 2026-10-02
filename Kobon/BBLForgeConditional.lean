import Kobon.BBLInfinite
import Kobon.BBLEvenInfinite
import Kobon.Universal

/-! Conditional instantiation for a compatible optimal 33-line seed.
The geometric seed premises remain explicit in this module. The historical
dyadic family is attributed to Forge--Ramírez Alfonsín; TamuraSeed33 is a
legacy internal certificate name. Polynomial comparisons are arithmetic,
not assertions of a global upper-bound theorem. -/
namespace Kobon.BBLForgeConditional
open BBLInfinite BBLEvenInfinite

def q (t : Nat) : Nat := 32*2^t
def oddCount (t : Nat) : Nat := (1024*4^t-1)/3
def evenCount (t : Nat) : Nat := oddCount t+16*2^t

theorem q_succ (t : Nat) : q (t+1)=2*q t := by unfold q; rw [pow_succ]; ring

theorem q_properties (t : Nat) : 32≤q t ∧ q t%2=0 ∧ q t%3≠0 := by
  induction t with
  | zero => norm_num [q]
  | succ t ih =>
    rw [q_succ]
    refine ⟨by omega,by omega,?_⟩
    have hm : q t%3=1 ∨ q t%3=2 := by omega
    rcases hm with hm | hm <;> simp [Nat.mul_mod,hm]

theorem q_square (t : Nat) : q t^2=1024*4^t := by
  have hp : (2^t)^2=4^t := by rw [← pow_mul,Nat.mul_comm t 2,pow_mul]; norm_num
  unfold q
  nlinarith [hp]

theorem count341_formula (t : Nat) : triangleCount 8 341 t=oddCount t := by
  have hh := triangleCount_identity 8 341 t
  have hs : (4*8*2^t)^2=1024*4^t := q_square t
  rw [hs] at hh
  unfold oddCount
  omega

theorem count_identity (t : Nat) : 3*oddCount t+1=q t^2 := by
  have hh := triangleCount_identity 8 341 t
  rw [count341_formula] at hh
  change 3*oddCount t+1=(32*2^t)^2
  norm_num at hh
  omega

theorem even_half (t : Nat) : evenCount t=oddCount t+q t/2 := by
  have hh : q t/2=16*2^t := by unfold q; omega
  simp only [evenCount,hh]

/-- A supplied actual 33-line seed family suffices for every odd dyadic level. -/
theorem odd_family (h : BBLInfinite.UniformSeed 8 341) (t : Nat) :
    SimpleLowerBound (q t+1) (oddCount t) := by
  have hh := BBLInfinite.infinite_family 8 341 (by decide) h t
  simpa only [q,count341_formula,show 4*8=32 by decide] using hh

/-- The enhanced seed family also supplies every full even exterior gain. -/
theorem even_family (w : Line ℝ) (hwa : 0<w.a)
    (h : BBLEvenInfinite.UniformVisibleSeed 8 341 16 w) (t : Nat) :
    SimpleLowerBound (q t+2) (evenCount t) := by
  have hh := BBLEvenInfinite.infinite_even_family 8 341 16 (by decide) w hwa h t
  have hv : visibleCount 8 16 t=16*2^t := visibleCount_full 8 t
  simpa only [q,evenCount,count341_formula,hv,show 4*8=32 by decide] using hh

theorem odd_baseline_gain (t : Nat) :
    oddCount t=Universal.baseline (q t+1)+(q t/3-1) := by
  have hq := q_properties t
  have hc := count_identity t
  have hp : (q t+1)*(q t+1-3)+q t+2=q t^2 := by
    have hh : q t+1-3+2=q t := by omega
    nlinarith
  rw [Universal.baseline_formula (q t+1) (by omega)]
  have hm : (q t+1)%2=1 := by omega
  rw [hm]
  omega

theorem even_baseline_gain (t : Nat) :
    evenCount t=Universal.baseline (q t+2)+(q t/2-q t/3-1) := by
  have hq := q_properties t
  have hc := count_identity t
  have hp : (q t+2)*(q t+2-3)+2=q t^2+q t := by
    have hh : q t+2-3+1=q t := by omega
    nlinarith
  rw [Universal.baseline_formula (q t+2) (by omega)]
  have hm : (q t+2)%2=0 := by omega
  rw [hm,even_half]
  omega

theorem strict_baseline_gain (t : Nat) :
    Universal.baseline (q t+1)<oddCount t ∧ Universal.baseline (q t+2)<evenCount t := by
  rw [odd_baseline_gain,even_baseline_gain]
  have hq := (q_properties t).1
  constructor <;> omega

theorem odd_polynomial_exact (t : Nat) :
    (q t+1)*(q t+1-2)/3=oddCount t := by
  have hq := (q_properties t).1
  have hc := count_identity t
  have hp : (q t+1)*(q t+1-2)+1=q t^2 := by
    have hh : q t+1-2+1=q t := by omega
    nlinarith
  omega

theorem even_simple_polynomial_exact (t : Nat) :
    (q t+2)*(2*(q t+2)-5)/6=evenCount t := by
  have hq := q_properties t
  have hc := count_identity t
  have hp : (q t+2)*(2*(q t+2)-5)+2=2*q t^2+3*q t := by
    have hh : 2*(q t+2)-5+1=2*q t := by omega
    nlinarith
  rw [even_half]
  omega

#print axioms odd_family
#print axioms even_family
#print axioms odd_baseline_gain
#print axioms even_baseline_gain
#print axioms odd_polynomial_exact
#print axioms even_simple_polynomial_exact
end Kobon.BBLForgeConditional
