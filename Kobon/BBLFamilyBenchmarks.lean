import Kobon.BBLVerifiedFamilies
import Kobon.Universal

/-! Exact arithmetic comparisons for the verified eleven-seed family.
The quadratic expressions called benchmarks below are numbers only. This
module does not assert a general upper-bound theorem for arrangements. -/
namespace Kobon.BBLFamilyBenchmarks

def q (t : Nat) : Nat := 10*2^t
def oddCount (t : Nat) : Nat := (q t^2-4)/3
def evenCount (t : Nat) : Nat := oddCount t+q t/2

theorem q_succ (t : Nat) : q (t+1)=2*q t := by unfold q; rw [pow_succ]; ring

theorem q_properties (t : Nat) : 10≤q t ∧ q t%2=0 ∧ q t%3≠0 := by
  induction t with
  | zero => norm_num [q]
  | succ t ih =>
    rw [q_succ]
    refine ⟨by omega,by omega,?_⟩
    have hm : q t%3=1 ∨ q t%3=2 := by omega
    rcases hm with hm | hm <;> simp [Nat.mul_mod,hm]

theorem count_identity (t : Nat) : 3*oddCount t+4=q t^2 := by
  have hq := q_properties t
  have hs : q t^2%3=1 := by
    have hm : q t%3=1 ∨ q t%3=2 := by omega
    rcases hm with hm | hm <;> simp [pow_two,Nat.mul_mod,hm]
  have hb : 4≤q t^2 := by nlinarith [hq.1]
  unfold oddCount
  omega

theorem odd_formula (t : Nat) : oddCount t=(100*4^t-4)/3 := by
  have hp : (2^t)^2=4^t := by rw [← pow_mul,Nat.mul_comm t 2,pow_mul]; norm_num
  have he : q t^2=100*4^t := by unfold q; nlinarith [hp]
  simp only [oddCount,he]

theorem even_formula (t : Nat) : evenCount t=(100*4^t-4)/3+5*2^t := by
  rw [evenCount,odd_formula]
  have he : q t/2=5*2^t := by unfold q; omega
  rw [he]

theorem odd_sound (t : Nat) : SimpleLowerBound (q t+1) (oddCount t) := by
  rw [odd_formula]
  exact BBLVerifiedFamilies.eleven_odd_family t

theorem even_sound (t : Nat) : SimpleLowerBound (q t+2) (evenCount t) := by
  rw [even_formula]
  exact BBLVerifiedFamilies.eleven_even_family t

/-- Exact gain over the proved all-order baseline at the odd family orders. -/
theorem odd_baseline_gain (t : Nat) :
    oddCount t=Universal.baseline (q t+1)+(q t/3-2) := by
  have hq := q_properties t
  have hc := count_identity t
  have hp : (q t+1)*(q t+1-3)+q t+2=q t^2 := by
    have hh : q t+1-3+2=q t := by omega
    nlinarith
  rw [Universal.baseline_formula (q t+1) (by omega)]
  have hmod : (q t+1)%2=1 := by omega
  rw [hmod]
  omega

/-- Exact gain over the proved all-order baseline at the even family orders. -/
theorem even_baseline_gain (t : Nat) :
    evenCount t=Universal.baseline (q t+2)+(q t/2-q t/3-2) := by
  have hq := q_properties t
  have hc := count_identity t
  have hp : (q t+2)*(q t+2-3)+2=q t^2+q t := by
    have hh : q t+2-3+1=q t := by omega
    nlinarith
  rw [Universal.baseline_formula (q t+2) (by omega)]
  have hmod : (q t+2)%2=0 := by omega
  rw [hmod]
  unfold evenCount
  omega

theorem odd_strict_gain (t : Nat) : Universal.baseline (q t+1)<oddCount t := by
  rw [odd_baseline_gain]
  have hq := (q_properties t).1
  omega

theorem even_strict_gain (t : Nat) (ht : 1≤t) :
    Universal.baseline (q t+2)<evenCount t := by
  rw [even_baseline_gain]
  have hq : 20≤q t := by
    obtain ⟨s,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : t≠0)
    rw [q_succ]
    have := (q_properties s).1
    omega
  omega

/-- Distance to the classical quadratic expression, with no upper claim. -/
theorem odd_polynomial_gap (t : Nat) :
    (q t+1)*(q t+1-2)/3=oddCount t+1 := by
  have hq := (q_properties t).1
  have hc := count_identity t
  have hp : (q t+1)*(q t+1-2)+1=q t^2 := by
    have hh : q t+1-2+1=q t := by omega
    nlinarith
  omega

/-- Distance to the even simple-arrangement benchmark, with no upper claim. -/
theorem even_simple_polynomial_gap (t : Nat) :
    (q t+2)*(2*(q t+2)-5)/6=evenCount t+1 := by
  have hq := q_properties t
  have hc := count_identity t
  have hp : (q t+2)*(2*(q t+2)-5)+2=2*q t^2+3*q t := by
    have hh : 2*(q t+2)-5+1=2*q t := by omega
    nlinarith
  unfold evenCount
  omega

/-- The previous release's whole verified envelope equals its general
baseline after its final finite exception. This is a repository comparison,
not a claim about all values known in the literature. -/
theorem previous_envelope (n : Nat) (hn : 195<n) :
    Universal.bound n=Universal.baseline n := by
  unfold Universal.bound
  rw [AllN.baseline_after_last_exception n hn]
  exact max_eq_left (Universal.classical_baseline_le n)

theorem odd_previous_gain (t : Nat) (hn : 195<q t+1) :
    oddCount t=Universal.bound (q t+1)+(q t/3-2) := by
  rw [previous_envelope _ hn]
  exact odd_baseline_gain t

theorem even_previous_gain (t : Nat) (hn : 195<q t+2) :
    evenCount t=Universal.bound (q t+2)+(q t/2-q t/3-2) := by
  rw [previous_envelope _ hn]
  exact even_baseline_gain t

theorem odd_previous_strict (t : Nat) (hn : 195<q t+1) :
    Universal.bound (q t+1)<oddCount t := by
  rw [previous_envelope _ hn]
  exact odd_strict_gain t

theorem even_previous_strict (t : Nat) (hn : 195<q t+2) :
    Universal.bound (q t+2)<evenCount t := by
  rw [even_previous_gain t hn]
  omega

theorem q_tail (t : Nat) : 320≤q (t+5) := by
  induction t with
  | zero => norm_num [q]
  | succ t ih =>
    rw [show t+1+5=(t+5)+1 by omega,q_succ]
    omega

/-- Infinitely many strict improvements over the entire old verified
release envelope, in both parities, starting at321 and322 lines. -/
theorem strict_previous_tail (t : Nat) :
    Universal.bound (q (t+5)+1)<oddCount (t+5) ∧
    Universal.bound (q (t+5)+2)<evenCount (t+5) := by
  have hq := q_tail t
  exact ⟨odd_previous_strict _ (by omega),even_previous_strict _ (by omega)⟩

#print axioms strict_previous_tail
#print axioms odd_baseline_gain
#print axioms even_baseline_gain
#print axioms odd_polynomial_gap
#print axioms even_simple_polynomial_gap
end Kobon.BBLFamilyBenchmarks
