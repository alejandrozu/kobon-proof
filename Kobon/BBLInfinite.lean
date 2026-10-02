import Kobon.BBLRecursiveSeed

/-! Finite-depth iteration of the BBL geometric seed invariant.
The positive epsilon interval can shrink with depth. No uniform positive
epsilon valid at every depth is assumed or asserted. -/
namespace Kobon.BBLInfinite
open Real BBLAnalytic BBLRecursiveSeed

def UniformSeed (r T : Nat) : Prop :=
  ∃ η : ℝ, 0<η ∧ ∀ ε : ℝ, 0<ε → ε<η → Compatible r T ε

theorem uniform_step (r T : Nat) (hr : 5≤r) (h : UniformSeed r T) :
    UniformSeed (2*r) (T+(4*r)^2) := by
  obtain ⟨η,hη,hseed⟩ := h
  obtain ⟨ha,ha2,_⟩ := alpha_data r hr
  have htan : 0<tan (alpha r/2) :=
    tan_pos_of_pos_of_lt_pi_div_two (by linarith) (by linarith [pi_pos])
  refine ⟨min η (tan (alpha r/2)),lt_min hη htan,?_⟩
  intro ε he hε
  exact compatible_step r T hr ε he (lt_of_lt_of_le hε (min_le_right _ _))
    (hseed ε he (lt_of_lt_of_le hε (min_le_left _ _)))

def triangleCount (r T : Nat) : Nat→Nat
  | 0 => T
  | t+1 => triangleCount r T t+(4*(r*2^t))^2

theorem index_lower (r t : Nat) (hr : 5≤r) : 5≤r*2^t := by
  have hp : 1≤2^t := Nat.one_le_pow t 2 (by decide)
  nlinarith

/-- Every finite depth has a whole nonempty interval of valid real seeds. -/
theorem uniform_iterate (r T : Nat) (hr : 5≤r) (h : UniformSeed r T) (t : Nat) :
    UniformSeed (r*2^t) (triangleCount r T t) := by
  induction t with
  | zero => simpa [triangleCount] using h
  | succ t ih =>
    have hh := uniform_step (r*2^t) (triangleCount r T t) (index_lower r t hr) ih
    have hi : r*2^(t+1)=2*(r*2^t) := by rw [pow_succ]; ring
    simpa only [hi,triangleCount] using hh

theorem uniform_lower_bound (r T : Nat) (h : UniformSeed r T) :
    SimpleLowerBound (4*r+1) T := by
  obtain ⟨η,hη,hseed⟩ := h
  exact seed_lower_bound r T (η/2) (hseed (η/2) (by linarith) (by linarith))

theorem infinite_family (r T : Nat) (hr : 5≤r) (h : UniformSeed r T) (t : Nat) :
    SimpleLowerBound (4*r*2^t+1) (triangleCount r T t) := by
  have hh := uniform_lower_bound (r*2^t) (triangleCount r T t) (uniform_iterate r T hr h t)
  simpa only [Nat.mul_assoc] using hh

/-- The construction preserves the exact quadratic deficit of its seed. -/
theorem triangleCount_identity (r T t : Nat) :
    3*triangleCount r T t+(4*r)^2=3*T+(4*r*2^t)^2 := by
  induction t with
  | zero => simp [triangleCount]
  | succ t ih =>
    simp only [triangleCount,pow_succ]
    nlinarith [sq_nonneg (4*r*2^t)]

theorem seed132_identity (t : Nat) :
    3*triangleCount 5 132 t+4=400*4^t := by
  have hh := triangleCount_identity 5 132 t
  have hpow : (2^t)^2=4^t := by rw [← pow_mul, Nat.mul_comm t 2, pow_mul]; norm_num
  have he : (4*5*2^t)^2=400*4^t := by nlinarith [hpow]
  rw [he] at hh
  omega

theorem seed132_formula (t : Nat) :
    triangleCount 5 132 t=(400*4^t-4)/3 := by
  have hh := seed132_identity t
  omega

#print axioms uniform_iterate
#print axioms infinite_family
#print axioms seed132_formula
end Kobon.BBLInfinite
