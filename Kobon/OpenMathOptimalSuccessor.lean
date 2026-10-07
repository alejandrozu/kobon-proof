import Kobon.OpenMathBoundarySuccessor

/-! Optimality transfer in the simple model, including the rounded odd
orders that have deficit two.  This is conditional on an actual optimal
odd witness; it does not assert the existence of such a witness for every
odd order, nor does it transfer unrestricted multiple-point optimality. -/
namespace Kobon.OpenMathOptimalSuccessor
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem successor_polynomial (m : Nat) (hm : 1≤m) :
    (2*m+1)*(2*m-1)/3+m=(2*m+2)*(4*m-1)/6 := by
  have hsub : 2*m-1+1=2*m := by omega
  have hsub' : 4*m-1+1=4*m := by omega
  have he : (2*m+2)*(4*m-1)=2*((2*m+1)*(2*m-1))+6*m := by
    nlinarith
  omega

/-- An actual simple arrangement at the rounded odd upper bound yields an
actual simple arrangement at the next even upper bound. -/
theorem optimal_odd_to_even (m : Nat) (hm : 1≤m)
    (h : SimpleLowerBound (2*m+1) ((2*m+1)*(2*m-1)/3)) :
    SimpleLowerBound (2*m+2) ((2*m+2)*(4*m-1)/6) := by
  have hdef : ((2*m+1 : Nat) : ℤ)*(2*m-1)-3*((2*m+1)*(2*m-1)/3 : Nat)≤2 := by
    have hd : (2*m+1)*(2*m-1)-3*((2*m+1)*(2*m-1)/3)≤2 := by omega
    have hsub : 1≤2*m := by omega
    have hle : 3*((2*m+1)*(2*m-1)/3)≤(2*m+1)*(2*m-1) := by omega
    have hdZ : (((2*m+1)*(2*m-1)-3*((2*m+1)*(2*m-1)/3) : Nat) : ℤ)≤2 := by
      exact_mod_cast hd
    simpa only [Nat.cast_sub hle,Nat.cast_mul,Nat.cast_sub hsub,Nat.cast_add,Nat.cast_ofNat,Nat.cast_one] using hdZ
  have he := OpenMathBoundarySuccessor.odd_defect_two_successor m
    ((2*m+1)*(2*m-1)/3) hm h hdef
  rw [successor_polynomial m hm] at he
  exact he

/-- The produced count is maximal among all simple certificates at that
even order.  This upper statement is restricted to the simple model. -/
theorem even_optimality (m T : Nat) (hm : 1≤m)
    (h : SimpleLowerBound (2*m+2) T) : T≤(2*m+2)*(4*m-1)/6 := by
  have hu := UpperEvenSimpleOptimality.simple_lower_bound_even_floor
    (2*m+2) T (by omega) (by omega) h
  have hs : 2*(2*m+2)-5=4*m-1 := by omega
  simpa only [hs] using hu

#print axioms successor_polynomial
#print axioms optimal_odd_to_even
#print axioms even_optimality
end Kobon.OpenMathOptimalSuccessor
