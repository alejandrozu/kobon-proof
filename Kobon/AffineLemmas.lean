import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Analytic lemmas used by the ordinary geometric proofs. -/
namespace Kobon.AffineLemmas

theorem positive_between_endpoints (a b E x : ℝ)
    (hx : 0 ≤ x) (hxe : x ≤ E) (h0 : 0 < a) (hE : 0 < a+b*E) :
    0 < a+b*x := by
  by_cases hb : 0 ≤ b
  · nlinarith [mul_nonneg hb hx]
  · have hb' : 0 ≤ -b := by linarith
    nlinarith [mul_nonneg hb' (sub_nonneg.mpr hxe)]

theorem negative_between_endpoints (a b E x : ℝ)
    (hx : 0 ≤ x) (hxe : x ≤ E) (h0 : a < 0) (hE : a+b*E < 0) :
    a+b*x < 0 := by
  have h := positive_between_endpoints (-a) (-b) E x hx hxe (by linarith) (by linarith)
  linarith

/-- An exterior line misses the entire closed triangle, not only its interior. -/
theorem exterior_preserves_triangle (u v w H a b c : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hs : a+b+c=1)
    (hu : u < H) (hv : v < H) (hw : w < H) : a*u+b*v+c*w < H := by
  have hH := congrArg (fun x : ℝ => x*H) hs
  have h1 := mul_nonneg ha (le_of_lt (sub_pos.mpr hu))
  have h2 := mul_nonneg hb (le_of_lt (sub_pos.mpr hv))
  have h3 := mul_nonneg hc (le_of_lt (sub_pos.mpr hw))
  by_cases hap : 0 < a
  · have h := mul_pos hap (sub_pos.mpr hu)
    nlinarith
  · by_cases hbp : 0 < b
    · have h := mul_pos hbp (sub_pos.mpr hv)
      nlinarith
    · have hcp : 0 < c := by linarith
      have h := mul_pos hcp (sub_pos.mpr hw)
      nlinarith

#print axioms positive_between_endpoints
#print axioms exterior_preserves_triangle

end Kobon.AffineLemmas
