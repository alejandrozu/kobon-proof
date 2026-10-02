import Kobon.Universal
import Kobon.BBLVerifiedFamilies
import Kobon.BBLFamilyBenchmarks

/-! An all-order bound retaining the previous release and the newly closed
geometric recursive families. The finite maximum is an elementary executable
definition; mathematically only the matching dyadic branch contributes. -/
namespace Kobon.RecursiveEnvelope
set_option autoImplicit false
set_option maxHeartbeats 1000000

def candidate (n t : Nat) : Nat :=
  if n=10*2^t+1 then (100*4^t-4)/3
  else if n=10*2^t+2 then (100*4^t-4)/3+5*2^t else 0

theorem candidate_sound (n t : Nat) : LowerBound n (candidate n t) := by
  unfold candidate
  split
  next h => rw [h]; exact (BBLVerifiedFamilies.eleven_odd_family t).classical
  next _ =>
    split
    next h => rw [h]; exact (BBLVerifiedFamilies.eleven_even_family t).classical
    next _ => exact AllN.zero_lower_bound n

def familyBound (n : Nat) : Nat→Nat
  | 0 => 0
  | t+1 => max (familyBound n t) (candidate n t)

theorem familyBound_sound (n k : Nat) : LowerBound n (familyBound n k) := by
  induction k with
  | zero => exact AllN.zero_lower_bound n
  | succ k ih =>
    simp only [familyBound]
    rcases le_total (familyBound n k) (candidate n k) with h | h
    · rw [max_eq_right h]; exact candidate_sound n k
    · rw [max_eq_left h]; exact ih

theorem candidate_le_familyBound (n t k : Nat) (h : t<k) :
    candidate n t≤familyBound n k := by
  induction k with
  | zero => omega
  | succ k ih =>
    by_cases he : t=k
    · subst t; exact le_max_right _ _
    · exact le_trans (ih (by omega)) (le_max_left _ _)

/-- The retained finite witnesses, the all-n trigonometric construction, and
the recursive odd/even family are all included. -/
def bound (n : Nat) : Nat := max (Universal.bound n) (familyBound n (n+1))

theorem all_n (n : Nat) : LowerBound n (bound n) := by
  unfold bound
  rcases le_total (Universal.bound n) (familyBound n (n+1)) with h | h
  · rw [max_eq_right h]; exact familyBound_sound n (n+1)
  · rw [max_eq_left h]; exact Universal.all_n n

theorem previous_le (n : Nat) : Universal.bound n≤bound n := le_max_left _ _

theorem candidate_le (n t : Nat) (h : t≤n) : candidate n t≤bound n :=
  le_trans (candidate_le_familyBound n t (n+1) (by omega)) (le_max_right _ _)

theorem odd_family_le (t : Nat) : (100*4^t-4)/3≤bound (10*2^t+1) := by
  have hp : t<2^t := Nat.lt_two_pow_self
  have h := candidate_le (10*2^t+1) t (by omega)
  simpa only [candidate,if_pos rfl,ite_true] using h

theorem even_family_le (t : Nat) : (100*4^t-4)/3+5*2^t≤bound (10*2^t+2) := by
  have hp : t<2^t := Nat.lt_two_pow_self
  have h := candidate_le (10*2^t+2) t (by omega)
  simpa only [candidate,if_neg (show 10*2^t+2≠10*2^t+1 by omega),if_pos rfl,ite_true] using h

/-- Strict gains over the complete old envelope at infinitely many orders. -/
theorem strict_previous_tail (t : Nat) :
    Universal.bound (10*2^(t+5)+1)<bound (10*2^(t+5)+1) ∧
    Universal.bound (10*2^(t+5)+2)<bound (10*2^(t+5)+2) := by
  have h := BBLFamilyBenchmarks.strict_previous_tail t
  simp only [BBLFamilyBenchmarks.q,BBLFamilyBenchmarks.odd_formula,
    BBLFamilyBenchmarks.even_formula] at h
  exact ⟨lt_of_lt_of_le h.1 (odd_family_le (t+5)),
    lt_of_lt_of_le h.2 (even_family_le (t+5))⟩

#print axioms candidate_sound
#print axioms all_n
#print axioms strict_previous_tail
end Kobon.RecursiveEnvelope
