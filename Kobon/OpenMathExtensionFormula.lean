import Kobon.OpenMathEveryOrderExtension

/-! A closed arithmetic form for the actual geometric successor rule.
The result is a minimum of two integer half-counts, not an unproved
half-order gain for every old arrangement. -/
namespace Kobon.OpenMathExtensionFormula
open Cells OpenMathQuantitativeSuccessor OpenMathEveryOrderExtension
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem ceiling_boundary_formula (n b : Nat) (hn : 1≤n) (hb : b≤n) :
    ((n-1)*b+2*n-1)/(2*n)=min (n/2) ((b+1)/2) := by
  have hpred : n-1+1=n := by omega
  have hden : 0<2*n := by omega
  have hnum : 1≤(n-1)*b+2*n := by omega
  have hnumsub : (n-1)*b+2*n-1+1=(n-1)*b+2*n := by omega
  by_cases he : b=n
  · subst b
    have hc := (Nat.div_eq_iff (by omega : 0<2)).mp (rfl : n/2=n/2)
    have hm : n/2≤(n+1)/2 := Nat.div_le_div_right (by omega)
    rw [min_eq_left hm]
    apply (Nat.div_eq_iff hden).mpr
    have hl := Nat.mul_le_mul_left n hc.1
    constructor
    · nlinarith
    · apply Nat.sub_le_sub_right _ 1
      apply Nat.add_le_add_right _ (2*n)
      have hnp : n-1≤n/2*2 := by omega
      have hmul := Nat.mul_le_mul_right n hnp
      convert hmul using 1 <;> ring
  · have hbn : b<n := by omega
    have hc := (Nat.div_eq_iff (by omega : 0<2)).mp (rfl : (b+1)/2=(b+1)/2)
    have hm : (b+1)/2≤n/2 := Nat.div_le_div_right (by omega)
    rw [min_eq_right hm]
    apply (Nat.div_eq_iff hden).mpr
    have hl := Nat.mul_le_mul_left n hc.1
    have hcb : b≤((b+1)/2)*2 := by omega
    have hu := Nat.mul_le_mul_left (n-1) hcb
    constructor
    · nlinarith
    · apply Nat.sub_le_sub_right _ 1
      apply Nat.add_le_add_right _ (2*n)
      calc
        (n-1)*b≤(n-1)*(((b+1)/2)*2) := hu
        _≤n*(((b+1)/2)*2) := Nat.mul_le_mul_right _ (Nat.sub_le _ _)
        _=((b+1)/2)*(2*n) := by ring

/-- For δ=n(n−2)−3T and b=max(3,n−δ), the certified gain is
min(floor(n/2),ceil(b/2)). Natural subtraction truncates at zero. -/
theorem stepGain_formula (n T : Nat) (hn : 3≤n) :
    stepGain n T=min (n/2) ((max 3 (n-deficit n T)+1)/2) := by
  unfold stepGain boundaryResource boundaryLower
  exact ceiling_boundary_formula n _ (by omega)
    (max_le (by omega) (Nat.sub_le _ _))

theorem closed_form_successor (n T : Nat) (hn : 3≤n)
    (h : SimpleLowerBound n T) :
    SimpleLowerBound (n+1)
      (T+min (n/2) ((max 3 (n-deficit n T)+1)/2)) := by
  simpa only [stepGain_formula n T hn] using
    OpenMathEveryOrderExtension.successor n T hn h

#print axioms ceiling_boundary_formula
#print axioms stepGain_formula
#print axioms closed_form_successor
end Kobon.OpenMathExtensionFormula
