import Kobon.BoundaryExtension
import Kobon.Exterior

/-! Exact arithmetic of the requested recurrence, and a resource obstruction.

`full_step_iteration` explicitly assumes `FullStepClaim K`. It proves its
closed-form consequence, not the missing universal geometric recurrence.
`no_infinite_full_gain_budget` concerns a stated resource inequality; the
identification of that resource with geometric exterior wedges is separate.
-/
namespace Kobon.Iteration

/-- Sum of floor(k/2) for 0 <= k < n. -/
def gainPrefix (n : Nat) : Nat := (n/2)*((n-1)/2)

theorem gainPrefix_succ (n : Nat) : gainPrefix (n+1)=gainPrefix n+n/2 := by
  cases n with
  | zero => decide
  | succ m =>
    simp only [gainPrefix,Nat.add_sub_cancel]
    by_cases h : m%2=0
    · have h1 : (m+1)/2=m/2 := by omega
      have h2 : (m+1+1)/2=m/2+1 := by omega
      rw [h1,h2]
      ring
    · have h1 : (m+1)/2=m/2+1 := by omega
      have h2 : (m+1+1)/2=m/2+1 := by omega
      rw [h1,h2]
      ring

theorem gainPrefix_closed (n : Nat) : gainPrefix n=(n-1)^2/4 := by
  cases n with
  | zero => decide
  | succ m =>
    simp only [gainPrefix,Nat.add_sub_cancel]
    by_cases h : m%2=0
    · have heq : m=2*(m/2) := by omega
      have h1 : (m+1)/2=m/2 := by omega
      have hs : m^2=(2*(m/2))^2 := congrArg (fun z : Nat => z^2) heq
      rw [h1]
      have hl : 4*(m/2*(m/2)) ≤ m^2 := by nlinarith
      have hu : m^2 < 4*(m/2*(m/2)+1) := by nlinarith
      omega
    · have heq : m=2*(m/2)+1 := by omega
      have h1 : (m+1)/2=m/2+1 := by omega
      have hs : m^2=(2*(m/2)+1)^2 := congrArg (fun z : Nat => z^2) heq
      rw [h1]
      have hl : 4*((m/2+1)*(m/2)) ≤ m^2 := by nlinarith
      have hu : m^2 < 4*((m/2+1)*(m/2)+1) := by nlinarith
      omega

theorem gainPrefix_monotone : Monotone gainPrefix := by
  apply monotone_nat_of_le_succ
  intro n
  rw [gainPrefix_succ]
  omega

/-- Conditional arithmetic, with the unproved recurrence visible as an input. -/
theorem full_step_iteration (K : Nat → Nat) (hstep : KobonBoundary.FullStepClaim K)
    (s T : Nat) (hs : 3 ≤ s) (hbase : T ≤ K s) (r : Nat) :
    T+(gainPrefix (s+r)-gainPrefix s) ≤ K (s+r) := by
  have haux : ∀ r, T+gainPrefix (s+r) ≤ K (s+r)+gainPrefix s := by
    intro r
    induction r with
    | zero => simpa using Nat.add_le_add_right hbase (gainPrefix s)
    | succ r ih =>
      have ht := hstep (s+r) (by omega)
      have hp := gainPrefix_succ (s+r)
      have heq : s+(r+1)=s+r+1 := by omega
      simp only [heq]
      omega
  have hmono := gainPrefix_monotone (show s≤s+r by omega)
  have h := haux r
  omega

theorem from_49_conditional (K : Nat → Nat) (hstep : KobonBoundary.FullStepClaim K)
    (hbase : 767 ≤ K 49) (n : Nat) (hn : 49 ≤ n) :
    (n-1)^2/4+191 ≤ K n := by
  have h := full_step_iteration K hstep 49 767 (by decide) hbase (n-49)
  have heq : 49+(n-49)=n := by omega
  rw [heq] at h
  norm_num [gainPrefix] at h
  have hp := gainPrefix_closed n
  dsimp [gainPrefix] at hp
  omega

/-- Natural-number implementation of the weaker boundary-defect manuscript rule. -/
def defectGain (n T : Nat) : Nat :=
  ((n-1)*max 3 (3*T-n*(n-3))+2*n-1)/(2*n)

def defectIterate (s T : Nat) : Nat → Nat
  | 0 => T
  | r+1 => defectIterate s T r+defectGain (s+r) (defectIterate s T r)

theorem requested_samples :
    gainPrefix 49+191=767 ∧ gainPrefix 50+191=791 ∧ gainPrefix 51+191=816 ∧
    gainPrefix 52+191=841 ∧ gainPrefix 60+191=1061 := by decide +kernel

theorem defect_samples :
    defectIterate 49 767 1=791 ∧ defectIterate 49 767 2=803 ∧
    defectIterate 49 767 3=805 ∧ defectIterate 49 767 11=821 := by decide +kernel

/-- A pool that gains at most two items per step cannot spend at least three
per step forever. No geometric interpretation is assumed in this theorem. -/
theorem no_infinite_full_gain_budget (s : Nat) (hs : 6 ≤ s) (b c : Nat → Nat)
    (hbudget : ∀ r, b (r+1)+c r ≤ b r+2)
    (hgain : ∀ r, (s+r)/2 ≤ c r) : False := by
  have hbound : ∀ r, b r+r ≤ b 0 := by
    intro r
    induction r with
    | zero => omega
    | succ r ih =>
      have h1 := hbudget r
      have h2 := hgain r
      omega
  have h := hbound (b 0+1)
  omega

/-- For a 49-line input with 47 wedges, two successive full gains would
already contradict the wedge budget and a final count of at least three. -/
theorem two_steps_49_obstruction (b1 b2 : Nat)
    (hfirst : b1+24 ≤ 47+2) (hsecond : b2+25 ≤ b1+2) (hthree : 3 ≤ b2) : False := by
  omega

#print axioms gainPrefix_closed
#print axioms full_step_iteration
#print axioms from_49_conditional
#print axioms no_infinite_full_gain_budget
end Kobon.Iteration
