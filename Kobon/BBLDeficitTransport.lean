import Kobon.BBLEvenInfinite
import Kobon.UpperEvenSimpleOptimality

/-! Deficit transport for actual BBL seed invariants.  A finite geometric
seed controls an entire dyadic family with a constant additive gap.  The
exterior family has a second, independently conserved visibility deficit.
These statements assume the geometric uniform seed, rather than a bare
point-count certificate or an unproved successor rule. -/
namespace Kobon.BBLDeficitTransport
open BBLInfinite BBLEvenInfinite
set_option autoImplicit false

def gridOrder (r t : Nat) : Nat := 4*r*2^t
def oddBenchmark (r t : Nat) : Nat := ((gridOrder r t)^2-1)/3
def evenBenchmark (r t : Nat) : Nat := oddBenchmark r t+gridOrder r t/2

theorem gridOrder_positive (r t : Nat) (hr : 1≤r) : 1≤gridOrder r t := by
  have hp : 1≤2^t := Nat.one_le_pow t 2 (by decide)
  dsimp [gridOrder]
  nlinarith

theorem gridOrder_successor (r t : Nat) : gridOrder r (t+1)=2*gridOrder r t := by
  unfold gridOrder
  rw [pow_succ]
  ring

theorem gridOrder_half (r t : Nat) : gridOrder r t/2=2*r*2^t := by
  have he : gridOrder r t=2*(2*r*2^t) := by unfold gridOrder; ring
  rw [he]
  omega

theorem benchmark_successor (r t : Nat) (hr : 1≤r) :
    oddBenchmark r (t+1)=oddBenchmark r t+(gridOrder r t)^2 := by
  have hp := gridOrder_positive r t hr
  have hs : 1≤(gridOrder r t)^2 := by nlinarith
  have hs2 : 1≤(2*gridOrder r t)^2 := by nlinarith
  have he : (2*gridOrder r t)^2-1=
      ((gridOrder r t)^2-1)+3*(gridOrder r t)^2 := by
    nlinarith [Nat.sub_add_cancel hs,Nat.sub_add_cancel hs2]
  unfold oddBenchmark
  rw [gridOrder_successor,he]
  omega

/-- Doubling preserves the exact additive gap from the odd polynomial. -/
theorem count_benchmark_identity (r T t : Nat) (hr : 1≤r) :
    triangleCount r T t+oddBenchmark r 0=T+oddBenchmark r t := by
  induction t with
  | zero => simp [triangleCount]
  | succ t ih =>
    have hi : (4*(r*2^t))^2=(gridOrder r t)^2 := by unfold gridOrder; ring
    rw [triangleCount,benchmark_successor r t hr,hi]
    omega

theorem count_constant_gap (r T t : Nat) (hr : 1≤r)
    (hT : T≤oddBenchmark r 0) :
    triangleCount r T t+(oddBenchmark r 0-T)=oddBenchmark r t := by
  have h := count_benchmark_identity r T t hr
  omega

theorem visible_constant_gap (r V t : Nat) (hV : V≤2*r) :
    visibleCount r V t+(2*r-V)=gridOrder r t/2 := by
  have h := visibleCount_identity r V t
  rw [gridOrder_half]
  omega

/-- The loss of exterior pairs adds to the seed's triangle deficit, and
neither loss grows with the doubling depth. -/
theorem even_constant_gap (r T V t : Nat) (hr : 1≤r)
    (hT : T≤oddBenchmark r 0) (hV : V≤2*r) :
    triangleCount r T t+visibleCount r V t+
      ((oddBenchmark r 0-T)+(2*r-V))=evenBenchmark r t := by
  have ht := count_constant_gap r T t hr hT
  have hv := visible_constant_gap r V t hV
  unfold evenBenchmark
  omega

theorem oddBenchmark_floor (r t : Nat) (hr : 1≤r) :
    oddBenchmark r t=(gridOrder r t+1)*(gridOrder r t+1-2)/3 := by
  have hp := gridOrder_positive r t hr
  have hs : 1≤(gridOrder r t)^2 := by nlinarith
  have hl : gridOrder r t+1-2=gridOrder r t-1 := by omega
  have he : (gridOrder r t+1)*(gridOrder r t-1)=(gridOrder r t)^2-1 := by
    nlinarith [Nat.sub_add_cancel hp,Nat.sub_add_cancel hs]
  unfold oddBenchmark
  rw [hl,he]

theorem evenBenchmark_floor (r t : Nat) (hr : 1≤r) :
    evenBenchmark r t=(gridOrder r t+2)*(2*(gridOrder r t+2)-5)/6 := by
  have hp := gridOrder_positive r t hr
  have hs : 1≤(gridOrder r t)^2 := by nlinarith
  have hh : gridOrder r t=2*(2*r*2^t) := by unfold gridOrder; ring
  have hl : 2*(gridOrder r t+2)-5=2*gridOrder r t-1 := by omega
  have hp2 : 1≤2*gridOrder r t := by omega
  have he : (gridOrder r t+2)*(2*gridOrder r t-1)=
      2*((gridOrder r t)^2-1)+6*(2*r*2^t) := by
    nlinarith [Nat.sub_add_cancel hp2,Nat.sub_add_cancel hs]
  unfold evenBenchmark oddBenchmark
  rw [gridOrder_half,hl,he]
  omega

/-- The odd deficit formula has an actual simple line arrangement at every
finite depth whenever the supplied uniform seed is geometrically realized. -/
theorem odd_family_constant_gap (r T : Nat) (hr : 5≤r)
    (h : UniformSeed r T) (hT : T≤oddBenchmark r 0) (t : Nat) :
    SimpleLowerBound (gridOrder r t+1)
      (oddBenchmark r t-(oddBenchmark r 0-T)) := by
  have hc := count_constant_gap r T t (by omega) hT
  have hf := infinite_family r T hr h t
  have he : triangleCount r T t=oddBenchmark r t-(oddBenchmark r 0-T) := by omega
  simpa only [gridOrder,he] using hf

/-- Both triangle and visibility losses remain constant in the actual even
family.  This theorem does not assume that a maximal visible fan exists. -/
theorem even_family_constant_gap (r T V : Nat) (hr : 5≤r)
    (w : Line ℝ) (hwa : 0<w.a) (h : UniformVisibleSeed r T V w)
    (hT : T≤oddBenchmark r 0) (hV : V≤2*r) (t : Nat) :
    SimpleLowerBound (gridOrder r t+2)
      (evenBenchmark r t-((oddBenchmark r 0-T)+(2*r-V))) := by
  have hc := even_constant_gap r T V t (by omega) hT hV
  have hf := infinite_even_family r T V hr w hwa h t
  have he : triangleCount r T t+visibleCount r V t=
      evenBenchmark r t-((oddBenchmark r 0-T)+(2*r-V)) := by omega
  simpa only [gridOrder,he] using hf

#print axioms odd_family_constant_gap
#print axioms even_family_constant_gap
#print axioms evenBenchmark_floor
end Kobon.BBLDeficitTransport
