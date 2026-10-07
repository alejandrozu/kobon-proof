import Kobon.UpperOpenMathFullCoreFans

/-! Strict convexity of squared Euclidean norm prevents a finite cluster
from closing under antipodal continuations beyond a between-point bridge.
This is geometric algebra; the arrangement wrapper must derive the bridges. -/
namespace Kobon.UpperOpenMathAntipodalEscape
open Cells FanGeometry Finset
set_option maxHeartbeats 1000000

def normSquare (p : Point) : ℝ := p.1^2+p.2^2
def distanceSquare (p b : Point) : ℝ := (p.1-b.1)^2+(p.2-b.2)^2
def oppositePoint (p b : Point) (s : ℝ) : Point :=
  (p.1-s*(b.1-p.1),p.2-s*(b.2-p.2))

theorem distanceSquare_nonnegative (p b : Point) : 0≤distanceSquare p b := by
  exact add_nonneg (sq_nonneg _) (sq_nonneg _)

theorem distanceSquare_positive (p b : Point) (hne : p≠b) : 0<distanceSquare p b := by
  have hx : p.1≠b.1 ∨ p.2≠b.2 := by
    by_contra hh
    push_neg at hh
    exact hne (Prod.ext hh.1 hh.2)
  unfold distanceSquare
  rcases hx with hx|hy
  · exact add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero (sub_ne_zero.mpr hx)) (sq_nonneg _)
  · exact add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_ne_zero (sub_ne_zero.mpr hy))

theorem between_norm_strict (p b u : Point) (k : ℝ) (hk : 0<k)
    (hne : p≠b) (hu : u=oppositePoint b p k) (hmax : normSquare u≤normSquare p) :
    normSquare b<normSquare p := by
  have identity : normSquare u-normSquare p=
      (1+k)*(normSquare b-normSquare p+k*distanceSquare p b) := by
    rw [hu]
    dsimp [normSquare,distanceSquare,oppositePoint]
    ring
  have hnonpos : (1+k)*(normSquare b-normSquare p+k*distanceSquare p b)≤0 := by
    rw [← identity]
    exact sub_nonpos.mpr hmax
  have hin : normSquare b-normSquare p+k*distanceSquare p b≤0 := by
    by_contra hh
    have hgt := mul_pos (by linarith : 0<1+k) (lt_of_not_ge hh)
    linarith
  have hpos := mul_pos hk (distanceSquare_positive p b hne)
  linarith

theorem opposite_norm_greater (p b q : Point) (s : ℝ) (hs : 0<s)
    (hb : normSquare b<normSquare p) (hq : q=oppositePoint p b s) :
    normSquare p<normSquare q := by
  have identity : normSquare q-normSquare p=
      s*(normSquare p-normSquare b)+s*(1+s)*distanceSquare p b := by
    rw [hq]
    dsimp [normSquare,distanceSquare,oppositePoint]
    ring
  have hfirst := mul_pos hs (sub_pos.mpr hb)
  have hsecond := mul_nonneg (mul_nonneg hs.le (by linarith : 0≤1+s)) (distanceSquare_nonnegative p b)
  linarith

def AntipodalBridge (P : Finset Point) (p : Point) : Prop :=
  ∃ b u q : Point, u∈P ∧ q∈P ∧ p≠b ∧
    ∃ k s : ℝ, 0<k ∧ 0<s ∧ u=oppositePoint b p k ∧ q=oppositePoint p b s

def Surrounded (P : Finset Point) (p : Point) : Prop :=
  ∀ w : Line ℝ, affineEval w p=0 → (w.a≠0 ∨ w.b≠0) →
    ∃ q∈P, affineEval w q<0

theorem surrounded_norm_escape (P : Finset Point) (p : Point) (hs : Surrounded P p) :
    ∃ q∈P, normSquare p<normSquare q := by
  by_cases hp : p.1=0 ∧ p.2=0
  · let w : Line ℝ := ⟨1,0,0⟩
    obtain ⟨q,hq,hneg⟩ := hs w (by simp [w,affineEval,hp.1]) (Or.inl (by norm_num [w]))
    have hx : q.1<0 := by simpa [w,affineEval] using hneg
    have hsq := sq_pos_of_ne_zero (ne_of_lt hx)
    refine ⟨q,hq,?_⟩
    dsimp [normSquare]
    rw [hp.1,hp.2]
    nlinarith [sq_nonneg q.2]
  · let w : Line ℝ := ⟨-p.1,-p.2,-normSquare p⟩
    have wp : affineEval w p=0 := by dsimp [w,affineEval,normSquare]; ring
    have valid : w.a≠0 ∨ w.b≠0 := by
      dsimp [w]
      by_contra hh
      push_neg at hh
      exact hp ⟨neg_eq_zero.mp hh.1,neg_eq_zero.mp hh.2⟩
    obtain ⟨q,hq,hneg⟩ := hs w wp valid
    have identity : normSquare q-normSquare p=
        distanceSquare p q-2*affineEval w q := by
      dsimp [normSquare,distanceSquare,affineEval,w]
      ring
    refine ⟨q,hq,?_⟩
    have hnon := distanceSquare_nonnegative p q
    linarith

theorem finite_mixed_escape_impossible (P : Finset Point) (nonempty : P.Nonempty)
    (escape : ∀ p∈P, Surrounded P p ∨ AntipodalBridge P p) : False := by
  classical
  obtain ⟨p,hp,hmax⟩ := exists_max_image P normSquare nonempty
  rcases escape p hp with hs|hb
  · obtain ⟨q,hq,hgt⟩ := surrounded_norm_escape P p hs
    have hh := hmax q hq
    linarith
  · obtain ⟨b,u,q,huP,hqP,hne,k,s,hk,hs,hu,hq⟩ := hb
    have hbsmall := between_norm_strict p b u k hk hne hu (hmax u huP)
    have hgt := opposite_norm_greater p b q s hs hbsmall hq
    have hh := hmax q hqP
    linarith

#print axioms between_norm_strict
#print axioms opposite_norm_greater
#print axioms finite_mixed_escape_impossible
end Kobon.UpperOpenMathAntipodalEscape
