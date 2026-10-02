import Kobon.BBLEvenRecursive
import Kobon.BBLInfinite

/-! Infinite iteration including the actual exterior visible-pair resource. -/
namespace Kobon.BBLEvenInfinite
open Real Exterior BBLAnalytic BBLInfinite BBLVisibleSeed BBLEvenRecursive

def UniformVisibleSeed (r T V : Nat) (w : Line ℝ) : Prop :=
  ∃ η : ℝ, 0<η ∧ ∀ ε : ℝ, 0<ε → ε<η → BBLVisibleSeed.Compatible r T V ε w

theorem uniform_step (r T V : Nat) (hr : 5≤r) (w : Line ℝ) (hwa : 0<w.a)
    (h : UniformVisibleSeed r T V w) :
    UniformVisibleSeed (2*r) (T+(4*r)^2) (V+2*r) w := by
  obtain ⟨η,hη,hseed⟩ := h
  obtain ⟨ha,ha2,_⟩ := alpha_data r hr
  have htan : 0<tan (alpha r/2) :=
    tan_pos_of_pos_of_lt_pi_div_two (by linarith) (by linarith [pi_pos])
  refine ⟨min η (tan (alpha r/2)),lt_min hη htan,?_⟩
  intro ε he hε
  obtain ⟨s⟩ := hseed ε he (lt_of_lt_of_le hε (min_le_left _ _))
  exact visible_seed_step r T V hr ε he (lt_of_lt_of_le hε (min_le_right _ _)) w hwa s

def visibleCount (r V : Nat) : Nat→Nat
  | 0 => V
  | t+1 => visibleCount r V t+2*(r*2^t)

theorem uniform_iterate (r T V : Nat) (hr : 5≤r) (w : Line ℝ) (hwa : 0<w.a)
    (h : UniformVisibleSeed r T V w) (t : Nat) :
    UniformVisibleSeed (r*2^t) (triangleCount r T t) (visibleCount r V t) w := by
  induction t with
  | zero => simpa [triangleCount,visibleCount] using h
  | succ t ih =>
    have hh := uniform_step (r*2^t) (triangleCount r T t) (visibleCount r V t)
      (index_lower r t hr) w hwa ih
    have hi : r*2^(t+1)=2*(r*2^t) := by rw [pow_succ]; ring
    simpa only [hi,triangleCount,visibleCount] using hh

theorem uniform_even_bound (r T V : Nat) (w : Line ℝ) (h : UniformVisibleSeed r T V w) :
    SimpleLowerBound (4*r+2) (T+V) := by
  obtain ⟨η,hη,hseed⟩ := h
  exact even_lower_bound r T V (η/2) w (hseed (η/2) (by linarith) (by linarith))

theorem infinite_even_family (r T V : Nat) (hr : 5≤r) (w : Line ℝ) (hwa : 0<w.a)
    (h : UniformVisibleSeed r T V w) (t : Nat) :
    SimpleLowerBound (4*r*2^t+2) (triangleCount r T t+visibleCount r V t) := by
  have hh := uniform_even_bound (r*2^t) (triangleCount r T t) (visibleCount r V t) w
    (uniform_iterate r T V hr w hwa h t)
  simpa only [Nat.mul_assoc] using hh

theorem visibleCount_identity (r V t : Nat) :
    visibleCount r V t+2*r=V+2*r*2^t := by
  induction t with
  | zero => simp [visibleCount]
  | succ t ih => simp only [visibleCount,pow_succ]; nlinarith

theorem visibleCount_full (r t : Nat) : visibleCount r (2*r) t=2*r*2^t := by
  have hh := visibleCount_identity r (2*r) t
  omega

#print axioms uniform_iterate
#print axioms infinite_even_family
end Kobon.BBLEvenInfinite
