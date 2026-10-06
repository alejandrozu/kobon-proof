import Kobon.RecursiveEnvelope
import Kobon.OpenMathConstructionForgeFamily
import Kobon.BBL49VerifiedFamilies
import Kobon.OpenMathConstructionParetoFamily61
import Kobon.OpenMathConstructionFamily37

/-! An executable lower bound for every natural order. The previous complete
envelope is retained, with the actual33/49 families and the stronger61 orbit.
This is a portfolio of certified constructions, not an arbitrary full-gain
one-line recurrence or a new numerical-priority claim for the older families.
-/
namespace Kobon.OpenMathConstructionEnvelope
set_option autoImplicit false
set_option maxHeartbeats 1000000

def forgeCandidate (n t : Nat) : Nat :=
  if n=BBLForgeConditional.q t+1 then BBLForgeConditional.oddCount t
  else if n=BBLForgeConditional.q t+2 then BBLForgeConditional.evenCount t else 0

def seed49Candidate (n t : Nat) : Nat :=
  if n=48*2^t+1 then 768*4^t-1
  else if n=48*2^t+2 then 768*4^t-1+24*2^t else 0

def seed61Candidate (n t : Nat) : Nat :=
  if n=OpenMathConstructionFamily61.q t+1 then OpenMathConstructionFamily61.oddCount t
  else if n=OpenMathConstructionFamily61.q t+2 then
    OpenMathConstructionParetoFamily61.evenCount t else 0

def seed37Candidate (n t : Nat) : Nat :=
  if n=OpenMathConstructionFamily37.q t+1 then OpenMathConstructionFamily37.oddCount t
  else if n=OpenMathConstructionFamily37.q t+2 then
    OpenMathConstructionFamily37.evenCount t else 0

theorem lower_max (n T U : Nat) (hT : LowerBound n T) (hU : LowerBound n U) :
    LowerBound n (max T U) := by
  rcases le_total T U with h | h
  · rw [max_eq_right h]; exact hU
  · rw [max_eq_left h]; exact hT

theorem forgeCandidate_sound (n t : Nat) : LowerBound n (forgeCandidate n t) := by
  unfold forgeCandidate
  split
  next h => rw [h]; exact (OpenMathConstructionForgeFamily.odd_family t).classical
  next _ =>
    split
    next h => rw [h]; exact (OpenMathConstructionForgeFamily.even_family t).classical
    next _ => exact AllN.zero_lower_bound n

theorem seed49Candidate_sound (n t : Nat) : LowerBound n (seed49Candidate n t) := by
  unfold seed49Candidate
  split
  next h => rw [h]; exact (BBL49VerifiedFamilies.odd_family t).classical
  next _ =>
    split
    next h => rw [h]; exact (BBL49VerifiedFamilies.even_family t).classical
    next _ => exact AllN.zero_lower_bound n

theorem seed61Candidate_sound (n t : Nat) : LowerBound n (seed61Candidate n t) := by
  unfold seed61Candidate
  split
  next h => rw [h]; exact (OpenMathConstructionFamily61.odd_family t).classical
  next _ =>
    split
    next h => rw [h]; exact OpenMathConstructionParetoFamily61.even_classical t
    next _ => exact AllN.zero_lower_bound n

theorem seed37Candidate_sound (n t : Nat) : LowerBound n (seed37Candidate n t) := by
  unfold seed37Candidate
  split
  next h => rw [h]; exact (OpenMathConstructionFamily37.odd_family t).classical
  next _ =>
    split
    next h => rw [h]; exact OpenMathConstructionFamily37.even_classical t
    next _ => exact AllN.zero_lower_bound n

def candidate (n t : Nat) : Nat :=
  max (forgeCandidate n t)
    (max (seed49Candidate n t) (max (seed37Candidate n t) (seed61Candidate n t)))

theorem candidate_sound (n t : Nat) : LowerBound n (candidate n t) :=
  lower_max n _ _ (forgeCandidate_sound n t)
    (lower_max n _ _ (seed49Candidate_sound n t)
      (lower_max n _ _ (seed37Candidate_sound n t) (seed61Candidate_sound n t)))

def familyBound (n : Nat) : Nat → Nat
  | 0 => 0
  | k+1 => max (familyBound n k) (candidate n k)

theorem familyBound_sound (n k : Nat) : LowerBound n (familyBound n k) := by
  induction k with
  | zero => exact AllN.zero_lower_bound n
  | succ k ih => exact lower_max n _ _ ih (candidate_sound n k)

def bound (n : Nat) : Nat := max (RecursiveEnvelope.bound n) (familyBound n (n+1))

/-- Every order has an actual nonparallel real-line witness for this value. -/
theorem all_n (n : Nat) : LowerBound n (bound n) :=
  lower_max n _ _ (RecursiveEnvelope.all_n n) (familyBound_sound n (n+1))

theorem previous_le (n : Nat) : RecursiveEnvelope.bound n≤bound n := le_max_left _ _

theorem baseline_le (n : Nat) : Universal.baseline n≤bound n := by
  exact le_trans (Universal.baseline_le n)
    (le_trans (RecursiveEnvelope.previous_le n) (previous_le n))

theorem candidate_le_familyBound (n t k : Nat) (ht : t<k) :
    candidate n t≤familyBound n k := by
  induction k with
  | zero => omega
  | succ k ih =>
    by_cases he : t=k
    · subst t; exact le_max_right _ _
    · exact le_trans (ih (by omega)) (le_max_left _ _)

theorem seed61Candidate_le (n t : Nat) (ht : t≤n) : seed61Candidate n t≤bound n := by
  have hc : seed61Candidate n t≤candidate n t :=
    le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
  exact le_trans hc (le_trans (candidate_le_familyBound n t (n+1) (by omega))
    (le_max_right _ _))

theorem odd_family_le (t : Nat) :
    OpenMathConstructionFamily61.oddCount t≤bound (OpenMathConstructionFamily61.q t+1) := by
  have hp : t<2^t := Nat.lt_two_pow_self
  have ht : t≤OpenMathConstructionFamily61.q t+1 := by
    unfold OpenMathConstructionFamily61.q
    omega
  have h := seed61Candidate_le (OpenMathConstructionFamily61.q t+1) t ht
  simpa only [seed61Candidate,if_pos rfl,ite_true] using h

theorem even_family_le (t : Nat) :
    OpenMathConstructionParetoFamily61.evenCount t≤
      bound (OpenMathConstructionFamily61.q t+2) := by
  have hp : t<2^t := Nat.lt_two_pow_self
  have ht : t≤OpenMathConstructionFamily61.q t+2 := by
    unfold OpenMathConstructionFamily61.q
    omega
  have h := seed61Candidate_le (OpenMathConstructionFamily61.q t+2) t ht
  simpa only [seed61Candidate,if_neg (show OpenMathConstructionFamily61.q t+2≠
    OpenMathConstructionFamily61.q t+1 by omega),if_pos rfl,ite_true] using h

theorem retains_old_even_family_plus_one (t : Nat) :
    OpenMathConstructionFamily61.evenCount t+1≤
      bound (OpenMathConstructionFamily61.q t+2) := even_family_le t

theorem odd_baseline_gain (t : Nat) :
    Universal.baseline (OpenMathConstructionFamily61.q t+1)+
      (OpenMathConstructionFamily61.q t/3-11)≤bound (OpenMathConstructionFamily61.q t+1) := by
  rw [← OpenMathConstructionFamily61.odd_baseline_gain t]
  exact odd_family_le t

theorem even_baseline_gain (t : Nat) (ht : 1≤t) :
    Universal.baseline (OpenMathConstructionFamily61.q t+2)+
      (OpenMathConstructionFamily61.q t/6-11)≤bound (OpenMathConstructionFamily61.q t+2) := by
  have h := even_family_le t
  rw [OpenMathConstructionParetoFamily61.even_baseline_gain t ht] at h
  exact h

/-- A uniform quadratic quality guarantee for the retained all-order bound.
This inherits the existing all-order construction; no new leading constant
or global upper-bound theorem is asserted. -/
theorem quadratic_lower (n : Nat) : n^2≤3*(bound n+n) := by
  by_cases hn : 4≤n
  · have hbase := baseline_le n
    rw [Universal.baseline_formula n hn] at hbase
    have hdiv : n*(n-3)≤3*(n*(n-3)/3)+2 := by omega
    have hsub : n-3+3=n := by omega
    have he : n*(n-3)+3*n=n^2 := by nlinarith
    omega
  · have hh : n*n≤n*3 := Nat.mul_le_mul_left n (by omega : n≤3)
    nlinarith

#print axioms all_n
#print axioms previous_le
#print axioms retains_old_even_family_plus_one
end Kobon.OpenMathConstructionEnvelope
