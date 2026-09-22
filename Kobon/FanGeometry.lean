import Kobon.Cells

/-!
# Geometric obstruction to a long ordinary-endpoint fan

This module proves the geometric propagation step used in the multiple-point
fan argument. Consecutive opposite triangle supports must be the same line
when their shared radial endpoint is ordinary. Consequently such a strip
cannot extend between opposite rays from its center. These are actual real
line-incidence statements, rather than assumptions about aggregate counts.

The extraction of a cyclic sector fan from an arbitrary arrangement, and its
counting consequences, remain separate from this module.
-/
namespace Kobon.FanGeometry

/-- Exactly two indexed arrangement lines pass through this point. -/
def OrdinaryAt (n : ℕ) (L : ℕ → Line ℝ) (p : Point) : Prop :=
  ∃ a b : Fin n, a≠b ∧ ∀ i : Fin n,
    affineEval (L i) p=0 ↔ i=a ∨ i=b

/-- At an ordinary point, two incident supports different from the radial
line must coincide. No global simplicity assumption is used. -/
theorem ordinary_nonradial_unique (n : ℕ) (L : ℕ → Line ℝ) (p : Point)
    (h : OrdinaryAt n L p) (R A B : Fin n)
    (hR : affineEval (L R) p=0)
    (hA : affineEval (L A) p=0) (hB : affineEval (L B) p=0)
    (hAR : A≠R) (hBR : B≠R) : A=B := by
  rcases h with ⟨a,b,hab,hi⟩
  rcases (hi R).mp hR with hr | hr
  · rcases (hi A).mp hA with ha | ha
    · exact False.elim (hAR (ha.trans hr.symm))
    · rcases (hi B).mp hB with hb | hb
      · exact False.elim (hBR (hb.trans hr.symm))
      · exact ha.trans hb.symm
  · rcases (hi A).mp hA with ha | ha
    · rcases (hi B).mp hB with hb | hb
      · exact ha.trans hb.symm
      · exact False.elim (hBR (hb.trans hr.symm))
    · exact False.elim (hAR (ha.trans hr.symm))

/-- A strip of triangles centered at c, described by its radial endpoints
and opposite supporting lines. Each opposite line contains consecutive
endpoints and avoids c, so those three vertices are noncollinear whenever
the radial endpoint is distinct from c. The indexed radial incidences are
included explicitly to connect the ordinary-point condition to the fan. -/
structure FanStrip (n m : ℕ) (L : ℕ → Line ℝ) where
  center : Point
  point : ℕ → Point
  radial : ℕ → Fin n
  opposite : ℕ → Fin n
  positive_length : 0<m
  radial_center : ∀ i, i≤m → affineEval (L (radial i)) center=0
  radial_point : ∀ i, i≤m → affineEval (L (radial i)) (point i)=0
  opposite_left : ∀ j, j<m → affineEval (L (opposite j)) (point j)=0
  opposite_right : ∀ j, j<m → affineEval (L (opposite j)) (point (j+1))=0
  opposite_avoids_center : ∀ j, j<m → affineEval (L (opposite j)) center≠0
  triangle_nondegenerate : ∀ j, j<m → areaDet center (point j) (point (j+1))≠0
  ordinary_internal : ∀ i, 0<i → i<m → OrdinaryAt n L (point i)

namespace FanStrip

/-- Construct a fan strip directly from actual real triangle geometries.
For certified arrangement faces, `Cells.ofPredicate` supplies these geometries. -/
def ofTriangles {n m : ℕ} {L : ℕ → Line ℝ}
    (c : Point) (P : ℕ → Point) (R A : ℕ → Fin n)
    (T : ℕ → Cells.TriangleGeometry) (hm : 0<m)
    (hR : ∀ i, i≤m → affineEval (L (R i)) c=0)
    (hP : ∀ i, i≤m → affineEval (L (R i)) (P i)=0)
    (hTp : ∀ j, j<m → (T j).p=c)
    (hTq : ∀ j, j<m → (T j).q=P j)
    (hTr : ∀ j, j<m → (T j).r=P (j+1))
    (hTA : ∀ j, j<m → (T j).A=L (A j))
    (hO : ∀ i, 0<i → i<m → OrdinaryAt n L (P i)) : FanStrip n m L where
  center := c
  point := P
  radial := R
  opposite := A
  positive_length := hm
  radial_center := hR
  radial_point := hP
  opposite_left := by
    intro j hj
    simpa only [hTA j hj,hTq j hj] using (T j).Aq
  opposite_right := by
    intro j hj
    simpa only [hTA j hj,hTr j hj] using (T j).Ar
  opposite_avoids_center := by
    intro j hj
    simpa only [hTA j hj,hTp j hj] using (T j).Ap
  triangle_nondegenerate := by
    intro j hj
    simpa only [hTp j hj,hTq j hj,hTr j hj] using (T j).nondegenerate
  ordinary_internal := hO

theorem adjacent_opposites_eq {n m : ℕ} {L : ℕ → Line ℝ}
    (f : FanStrip n m L) (j : ℕ) (hj : j+1<m) :
    f.opposite (j+1)=f.opposite j := by
  apply ordinary_nonradial_unique n L (f.point (j+1))
    (f.ordinary_internal (j+1) (by omega) hj) (f.radial (j+1))
  · exact f.radial_point _ (by omega)
  · exact f.opposite_left _ hj
  · exact f.opposite_right _ (by omega)
  · intro h
    have hc := f.radial_center (j+1) (by omega)
    rw [← h] at hc
    exact f.opposite_avoids_center _ hj hc
  · intro h
    have hc := f.radial_center (j+1) (by omega)
    rw [← h] at hc
    exact f.opposite_avoids_center _ (by omega) hc

theorem all_opposites_eq {n m : ℕ} {L : ℕ → Line ℝ}
    (f : FanStrip n m L) (j : ℕ) (hj : j<m) :
    f.opposite j=f.opposite 0 := by
  induction j with
  | zero => rfl
  | succ j ih => exact (f.adjacent_opposites_eq j hj).trans (ih (by omega))

theorem outer_endpoints_on_one_line {n m : ℕ} {L : ℕ → Line ℝ}
    (f : FanStrip n m L) :
    affineEval (L (f.opposite 0)) (f.point 0)=0 ∧
    affineEval (L (f.opposite 0)) (f.point m)=0 := by
  constructor
  · exact f.opposite_left 0 f.positive_length
  · have h := f.opposite_right (m-1) (by have := f.positive_length; omega)
    rw [f.all_opposites_eq (m-1) (by have := f.positive_length; omega)] at h
    have hm : m-1+1=m := by have := f.positive_length; omega
    simpa only [hm] using h

/-- The center cannot lie anywhere on the affine line through the two outer
endpoints. In particular, those endpoints cannot lie on opposite radial rays. -/
theorem center_not_affine_combination {n m : ℕ} {L : ℕ → Line ℝ}
    (f : FanStrip n m L) (t : ℝ) :
    f.center≠barycenter (f.point 0) (f.point m) (f.point 0) (1-t) t 0 := by
  intro he
  have hc := f.opposite_avoids_center 0 f.positive_length
  rcases f.outer_endpoints_on_one_line with ⟨h0,hm⟩
  apply hc
  rw [he,affineEval_barycenter _ _ _ _ _ _ _ (by ring),h0,hm]
  ring

end FanStrip

/-- A real line avoiding c cannot meet both opposite open rays from c. -/
theorem line_not_both_opposite_rays (l : Line ℝ) (c d : Point) (u v : ℝ)
    (hu : 0<u) (hv : 0<v) (hc : affineEval l c≠0)
    (hp : affineEval l (c.1+u*d.1,c.2+u*d.2)=0) :
    affineEval l (c.1-v*d.1,c.2-v*d.2)≠0 := by
  intro hq
  have hcomb : (u+v)*affineEval l c=0 := by
    dsimp [affineEval] at *
    nlinarith [congrArg (fun z : ℝ => v*z) hp,
      congrArg (fun z : ℝ => u*z) hq]
  exact hc ((mul_eq_zero.mp hcomb).resolve_left (by positivity))

/-- A run of ordinary radial endpoints cannot connect opposite outer rays.
In an r-line cyclic fan, a putative run of r-1 ordinary shared rays supplies
such a strip with m=r. The cyclic extraction itself is not assumed proved here. -/
theorem no_opposite_end_fan {n m : ℕ} {L : ℕ → Line ℝ}
    (f : FanStrip n m L) (d : Point) (u v : ℝ) (hu : 0<u) (hv : 0<v)
    (hp : f.point 0=(f.center.1+u*d.1,f.center.2+u*d.2)) :
    f.point m≠(f.center.1-v*d.1,f.center.2-v*d.2) := by
  intro hq
  rcases f.outer_endpoints_on_one_line with ⟨h0,hm⟩
  rw [hp] at h0
  rw [hq] at hm
  exact line_not_both_opposite_rays (L (f.opposite 0)) f.center d u v hu hv
    (f.opposite_avoids_center 0 f.positive_length) h0 hm

#print axioms ordinary_nonradial_unique
#print axioms FanStrip.all_opposites_eq
#print axioms FanStrip.center_not_affine_combination
#print axioms no_opposite_end_fan

end Kobon.FanGeometry
