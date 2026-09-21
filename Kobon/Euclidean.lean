import Kobon.Geometry
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-! Affine interpretation of the certificate predicate. -/
namespace Kobon

abbrev Point := ℝ × ℝ

def affineEval (l : Line ℝ) (p : Point) : ℝ := l.a*p.1+l.b*p.2-l.c

noncomputable def intersection (l m : Line ℝ) : Point :=
  ((vertex l m).1 / det l m, (vertex l m).2.1 / det l m)

def areaDet (p q r : Point) : ℝ :=
  (q.1-p.1)*(r.2-p.2)-(q.2-p.2)*(r.1-p.1)

def barycenter (p q r : Point) (u v w : ℝ) : Point :=
  (u*p.1+v*q.1+w*r.1,u*p.2+v*q.2+w*r.2)

theorem intersection_on_left (l m : Line ℝ) (h : det l m ≠ 0) :
    affineEval l (intersection l m) = 0 := by
  dsimp [affineEval,intersection,vertex]
  field_simp
  dsimp [det] at *
  nlinarith

theorem intersection_on_right (l m : Line ℝ) (h : det l m ≠ 0) :
    affineEval m (intersection l m) = 0 := by
  dsimp [affineEval,intersection,vertex]
  field_simp
  dsimp [det] at *
  nlinarith

theorem eval_intersection (r l m : Line ℝ) (h : det l m ≠ 0) :
    affineEval r (intersection l m) = evalVertex r l m / det l m := by
  dsimp [affineEval,intersection,evalVertex,vertex]
  field_simp

theorem area_intersections (l m r : Line ℝ)
    (h1 : det l m ≠ 0) (h2 : det l r ≠ 0) (h3 : det m r ≠ 0) :
    areaDet (intersection l m) (intersection l r) (intersection m r) =
      (evalVertex r l m)^2 / (det l m*det l r*det m r) := by
  dsimp [areaDet,intersection,vertex,evalVertex]
  field_simp
  dsimp [det]
  ring

theorem supporting_triangle_nondegenerate (l m r : Line ℝ)
    (h1 : det l m ≠ 0) (h2 : det l r ≠ 0) (h3 : det m r ≠ 0)
    (ht : evalVertex r l m ≠ 0) :
    areaDet (intersection l m) (intersection l r) (intersection m r) ≠ 0 := by
  rw [area_intersections l m r h1 h2 h3]
  exact div_ne_zero (pow_ne_zero _ ht) (mul_ne_zero (mul_ne_zero h1 h2) h3)

theorem affineEval_barycenter (l : Line ℝ) (p q r : Point) (u v w : ℝ)
    (hs : u+v+w=1) :
    affineEval l (barycenter p q r u v w) =
      u*affineEval l p+v*affineEval l q+w*affineEval l r := by
  dsimp [affineEval,barycenter]
  have h := congrArg (fun x : ℝ => x*l.c) hs
  nlinarith

theorem same_halfplane_barycenter (l : Line ℝ) (p q r : Point) (u v w : ℝ)
    (hu : 0 ≤ u) (hv : 0 ≤ v) (hw : 0 ≤ w) (hs : u+v+w=1)
    (hp : 0 ≤ affineEval l p) (hq : 0 ≤ affineEval l q) (hr : 0 ≤ affineEval l r) :
    0 ≤ affineEval l (barycenter p q r u v w) := by
  rw [affineEval_barycenter l p q r u v w hs]
  exact add_nonneg (add_nonneg (mul_nonneg hu hp) (mul_nonneg hv hq)) (mul_nonneg hw hr)

theorem oriented_nonneg_iff (r l m : Line ℝ) (h : det l m ≠ 0) :
    0 ≤ orientedEval r l m ↔ 0 ≤ affineEval r (intersection l m) := by
  rw [orientedEval_affine r l m h]
  exact mul_nonneg_iff_of_pos_right (sq_pos_of_ne_zero h)

theorem oriented_nonpos_iff (r l m : Line ℝ) (h : det l m ≠ 0) :
    orientedEval r l m ≤ 0 ↔ affineEval r (intersection l m) ≤ 0 := by
  rw [orientedEval_affine r l m h]
  have hp := sq_pos_of_ne_zero h
  change affineEval r (intersection l m) * (det l m)^2 ≤ 0 ↔ _
  constructor
  · intro hs
    nlinarith
  · intro hs
    exact mul_nonpos_of_nonpos_of_nonneg hs (le_of_lt hp)

theorem three_zeros_force_zero_normal (l : Line ℝ) (p q r : Point)
    (ha : areaDet p q r ≠ 0)
    (hp : affineEval l p = 0) (hq : affineEval l q = 0) (hr : affineEval l r = 0) :
    l.a = 0 ∧ l.b = 0 := by
  have h1 : l.a * areaDet p q r =
      (affineEval l q-affineEval l p)*(r.2-p.2)-
      (affineEval l r-affineEval l p)*(q.2-p.2) := by
    dsimp [affineEval,areaDet]
    ring
  have h2 : l.b * areaDet p q r =
      (affineEval l r-affineEval l p)*(q.1-p.1)-
      (affineEval l q-affineEval l p)*(r.1-p.1) := by
    dsimp [affineEval,areaDet]
    ring
  simp only [hp,hq,hr,sub_self,zero_mul] at h1 h2
  exact ⟨(mul_eq_zero.mp h1).resolve_right ha,(mul_eq_zero.mp h2).resolve_right ha⟩

theorem positive_weighted_sum (a b c u v w : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hn : ¬ (a=0 ∧ b=0 ∧ c=0)) (hu : 0 < u) (hv : 0 < v) (hw : 0 < w) :
    0 < u*a+v*b+w*c := by
  have h1 := mul_nonneg (le_of_lt hu) ha
  have h2 := mul_nonneg (le_of_lt hv) hb
  have h3 := mul_nonneg (le_of_lt hw) hc
  by_cases hap : 0 < a
  · have h := mul_pos hu hap
    linarith
  · by_cases hbp : 0 < b
    · have h := mul_pos hv hbp
      linarith
    · have hcp : 0 < c := by
        by_contra h
        exact hn ⟨by linarith,by linarith,by linarith⟩
      have h := mul_pos hw hcp
      linarith

/-- A nonzero line with one weak sign on the vertices does not meet the
open barycentric interior of a nondegenerate triangle. -/
theorem triangle_interior_uncut (l : Line ℝ) (p q r : Point)
    (hvalid : l.a ≠ 0 ∨ l.b ≠ 0) (ha : areaDet p q r ≠ 0)
    (u v w : ℝ) (hu : 0 < u) (hv : 0 < v) (hw : 0 < w) (hs : u+v+w=1)
    (hside : (0 ≤ affineEval l p ∧ 0 ≤ affineEval l q ∧ 0 ≤ affineEval l r) ∨
      (affineEval l p ≤ 0 ∧ affineEval l q ≤ 0 ∧ affineEval l r ≤ 0)) :
    affineEval l (barycenter p q r u v w) ≠ 0 := by
  have hn : ¬ (affineEval l p=0 ∧ affineEval l q=0 ∧ affineEval l r=0) := by
    rintro ⟨hp,hq,hr⟩
    have h := three_zeros_force_zero_normal l p q r ha hp hq hr
    rcases hvalid with hv | hv
    · exact hv h.1
    · exact hv h.2
  rw [affineEval_barycenter l p q r u v w hs]
  rcases hside with ⟨hp,hq,hr⟩ | ⟨hp,hq,hr⟩
  · exact ne_of_gt (positive_weighted_sum _ _ _ _ _ _ hp hq hr hn hu hv hw)
  · have hn' : ¬ (-affineEval l p=0 ∧ -affineEval l q=0 ∧ -affineEval l r=0) := by
      simpa only [neg_eq_zero] using hn
    have h := positive_weighted_sum (-affineEval l p) (-affineEval l q) (-affineEval l r)
      u v w (by linarith) (by linarith) (by linarith) hn' hu hv hw
    intro heq
    nlinarith

#print axioms supporting_triangle_nondegenerate
#print axioms same_halfplane_barycenter
#print axioms triangle_interior_uncut

end Kobon
