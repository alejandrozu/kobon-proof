import Kobon.OpenMathBoundaryMinimum

/-! Unconditional geometric extension at every next order in the simple
model, with a strictly positive resource even for low-density witnesses.
This is a quantitative recurrence, not the still unproved universal
half-order recurrence.  All input witnesses remain ordinary real lines. -/
namespace Kobon.OpenMathEveryOrderExtension
open Cells FanGeometry UpperVertexBudget OpenMathSimpleBoundary
  OpenMathBoundaryMinimum OpenMathQuantitativeSuccessor
set_option autoImplicit false
set_option maxHeartbeats 1000000

def boundaryResource (n T : Nat) : Nat := max 3 (boundaryLower n T)
def stepGain (n T : Nat) : Nat := ((n-1)*boundaryResource n T+2*n-1)/(2*n)

theorem certificate_boundary_resource (n T : Nat) (L : Nat → Line ℝ)
    (hp : NoParallel n L) (hs : NoConcurrent n L) (hn : 3≤n)
    (ts : List Triple) (hnd : ts.Nodup)
    (ht : ∀ t∈ts, TrianglePredicate n L t) (hc : T≤ts.length) :
    boundaryResource n T≤(doubleTerminals n L).card := by
  have hcap := UpperSimpleOptimality.simple_lower_bound_upper n T (by omega)
    ⟨L,hp,hs,ts,hnd,ht,hc⟩
  have hb := certificate_boundary_defect n L hp hs hn ts.get
    hnd.injective_get (fun i => ht _ (List.get_mem ts i))
  simp only [Fintype.card_fin] at hb
  have hcount : (T : ℤ)≤ts.length := by exact_mod_cast hc
  have hdefcast : ((deficit n T : Nat) : ℤ)=(n : ℤ)*(n-2)-3*T := by
    unfold deficit
    rw [Nat.cast_sub hcap]
    simp only [Nat.cast_mul,Nat.cast_sub (by omega : 2≤n),Nat.cast_ofNat]
  have hbz : (n : ℤ)-(deficit n T : ℤ)≤(doubleTerminals n L).card := by
    rw [hdefcast]
    linarith
  have hB : boundaryLower n T≤(doubleTerminals n L).card := by
    unfold boundaryLower
    by_cases hd : deficit n T≤n
    · have hcB : ((n-deficit n T : Nat) : ℤ)=(n : ℤ)-(deficit n T : ℤ) := Nat.cast_sub hd
      rw [←hcB] at hbz
      exact_mod_cast hbz
    · omega
  exact max_le (double_terminal_minimum n L hp hs hn) hB

/-- Starting from any supplied simple arrangement with n≥3, the next order
has at least T+ceil((n−1)max(3,n−δ)/(2n)) triangles, where δ=n(n−2)−3T. -/
theorem successor (n T : Nat) (hn : 3≤n) (h : SimpleLowerBound n T) :
    SimpleLowerBound (n+1) (T+stepGain n T) := by
  obtain ⟨L,hp,hs,ts,hnd,ht,hc⟩ := h
  exact extension_of_boundary_lower n T (boundaryResource n T) L hp hs (by omega)
    ts hnd ht hc (certificate_boundary_resource n T L hp hs hn ts hnd ht hc)

theorem stepGain_at_least_two (n T : Nat) (hn : 4≤n) : 2≤stepGain n T := by
  have hB : 3≤boundaryResource n T := le_max_left _ _
  have hprod := Nat.mul_le_mul_left (n-1) hB
  have hpred : n-1+1=n := by omega
  have hnpos : 0<2*n := by omega
  unfold stepGain
  rw [Nat.le_div_iff_mul_le hnpos]
  omega

/-- A count-independent consequence that can be repeated without any
boundary-form hypothesis: every simple witness of order at least four has
a simple successor with two additional triangles. -/
theorem successor_two (n T : Nat) (hn : 4≤n) (h : SimpleLowerBound n T) :
    SimpleLowerBound (n+1) (T+2) :=
  (successor n T (by omega) h).mono (Nat.add_le_add_left (stepGain_at_least_two n T hn) T)

theorem infinite_linear_extension (n T : Nat) (hn : 4≤n)
    (h : SimpleLowerBound n T) (k : Nat) :
    SimpleLowerBound (n+k) (T+2*k) := by
  induction k with
  | zero => simpa using h
  | succ k ih =>
    have he := successor_two (n+k) (T+2*k) (by omega) ih
    convert he using 1 <;> omega

def iteratedCount (n T : Nat) : Nat → Nat
  | 0 => T
  | k+1 => iteratedCount n T k+stepGain (n+k) (iteratedCount n T k)

/-- The quantitative step itself, with both parities, can be iterated to
every larger natural order. No subsequent optimality hypothesis is used. -/
theorem infinite_quantitative_extension (n T : Nat) (hn : 3≤n)
    (h : SimpleLowerBound n T) (k : Nat) :
    SimpleLowerBound (n+k) (iteratedCount n T k) := by
  induction k with
  | zero => simpa [iteratedCount] using h
  | succ k ih =>
    have he := successor (n+k) (iteratedCount n T k) (by omega) ih
    simpa only [iteratedCount,Nat.add_assoc] using he

#print axioms certificate_boundary_resource
#print axioms successor
#print axioms successor_two
#print axioms infinite_quantitative_extension
end Kobon.OpenMathEveryOrderExtension
