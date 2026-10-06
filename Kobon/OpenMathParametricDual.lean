import Kobon.Parametric
import Mathlib.Tactic

/-! Interval-certified dual separation for parametric construction cells.
A weighted combination of linear constraints gives a lower budget. The
coefficient box and a small epsilon interval give a strict upper budget.
The contradiction applies even when the unknown slope vector depends on
epsilon. It excludes the specified constraints, not all Kobon arrangements.
-/
namespace Kobon.OpenMathParametricDual
open Parametric Finset
set_option autoImplicit false
set_option maxHeartbeats 1000000

def envelope {d : Nat} (lo hi f : Form d) : ℚ := max |lower lo hi f| |upper lo hi f|

theorem abs_evaluate_le {d : Nat} (lo hi f : Form d) (x : Fin d → ℝ)
    (hx : InBox lo hi x) : |evaluate f x|≤(envelope lo hi f : ℝ) := by
  have he : (envelope lo hi f : ℝ)=
      max |(lower lo hi f : ℝ)| |(upper lo hi f : ℝ)| := by
    simp only [envelope,Rat.cast_max,Rat.cast_abs]
  rw [he]
  refine abs_le.mpr ⟨?_,?_⟩
  · exact (neg_le_neg (le_max_left _ _)).trans
      ((neg_abs_le _).trans (lower_le lo hi f x hx))
  · exact (le_upper lo hi f x hx).trans ((le_abs_self _).trans (le_max_right _ _))

theorem affine_product_upper (a w u e : ℝ) (he : 0≤e) (hu : |u|≤1) :
    (a+e*w)*u≤|a|+e*|w| := by
  calc
    (a+e*w)*u≤|(a+e*w)*u| := le_abs_self _
    _=|a+e*w| * |u| := abs_mul _ _
    _≤|a+e*w| * 1 := mul_le_mul_of_nonneg_left hu (abs_nonneg _)
    _=|a+e*w| := mul_one _
    _≤|a|+e*|w| := by
      have h1 := neg_abs_le a
      have h2 := le_abs_self a
      have h3 := neg_abs_le (e*w)
      have h4 := le_abs_self (e*w)
      have hh : |a+e*w|≤|a|+|e*w| := abs_le.mpr ⟨by linarith,by linarith⟩
      simpa only [abs_mul,abs_of_nonneg he] using hh

theorem budget_upper {d q : Nat} (lo hi : Form d) (f : Fin q → Form d)
    (w : Fin q → ℚ) (x : Fin d → ℝ) (hx : InBox lo hi x)
    (u : Fin q → ℝ) (hu : ∀ i, |u i|≤1) (e : ℝ) (he : 0≤e) :
    (∑ i, (evaluate (f i) x+e*(w i : ℝ))*u i)≤
      ((∑ i, envelope lo hi (f i) : ℚ) : ℝ)+e*((∑ i, |w i| : ℚ) : ℝ) := by
  calc
    (∑ i, (evaluate (f i) x+e*(w i : ℝ))*u i)≤
        ∑ i, (|evaluate (f i) x|+e*|(w i : ℝ)|) := by
      exact sum_le_sum (fun i _ => affine_product_upper _ _ _ e he (hu i))
    _≤∑ i, ((envelope lo hi (f i) : ℝ)+e*|(w i : ℝ)|) := by
      exact sum_le_sum (fun i _ => add_le_add (abs_evaluate_le lo hi (f i) x hx) (le_refl _))
    _=((∑ i, envelope lo hi (f i) : ℚ) : ℝ)+e*((∑ i, |w i| : ℚ) : ℝ) := by
      simp only [sum_add_distrib,mul_sum,Rat.cast_sum,Rat.cast_abs]

/-- A strict rational dual margin excludes every slope vector in the whole
box at every epsilon up to eta, including epsilon-dependent vectors. -/
theorem no_budget {d q : Nat} (lo hi : Form d) (f : Fin q → Form d)
    (w : Fin q → ℚ) (b eta : ℚ)
    (hgap : (∑ i, envelope lo hi (f i))+eta*(∑ i, |w i|)<b)
    (x : Fin d → ℝ) (hx : InBox lo hi x) (u : Fin q → ℝ)
    (hu : ∀ i, |u i|≤1) (e : ℝ) (he : 0≤e) (heta : e≤(eta : ℝ)) :
    ¬(b : ℝ)≤∑ i, (evaluate (f i) x+e*(w i : ℝ))*u i := by
  intro hb
  have hs : (0 : ℝ)≤((∑ i, |w i| : ℚ) : ℝ) := by positivity
  have hm := mul_le_mul_of_nonneg_right heta hs
  have hp : ((∑ i, envelope lo hi (f i) : ℚ) : ℝ)+
      (eta : ℝ)*((∑ i, |w i| : ℚ) : ℝ)<(b : ℝ) := by
    exact_mod_cast hgap
  have h := budget_upper lo hi f w x hx u hu e he
  linarith

#print axioms no_budget
end Kobon.OpenMathParametricDual
