import Kobon.FanCount

/-!
# A geometric cyclic fan has at most 2r-3 ordinary shared rays

This module connects actual real-line geometry to the cyclic counting lemma.
The input records the 2r radial elementary endpoints at an r-fold point,
antipodal rays, and the triangular sectors adjacent to every selected ordinary
shared ray. The no-long-run property is proved from this geometry, not assumed.

Constructing these cyclic data from an arbitrary finite affine arrangement
remains a separate obligation. No global Kobon upper bound is asserted here.
-/
namespace Kobon.CyclicFan
open FanGeometry

/-- Local geometric data around a multiple point. Selected rays represent
shared sides with ordinary other endpoints. All data concern actual real
points and indexed supporting lines. -/
structure Geometry (n r : ℕ) [NeZero (2*r)] (L : ℕ → Line ℝ) where
  center : Point
  point : ZMod (2*r) → Point
  radial : ZMod (2*r) → Fin n
  opposite : ZMod (2*r) → Fin n
  selected : Finset (ZMod (2*r))
  radial_center : ∀ z, affineEval (L (radial z)) center=0
  radial_point : ∀ z, affineEval (L (radial z)) (point z)=0
  ordinary : ∀ z, z∈selected → OrdinaryAt n L (point z)
  antipodal : ∀ z, ∃ v : ℝ, 0<v ∧
    point (z+(r : ZMod (2*r)))=
      (center.1-v*((point z).1-center.1),center.2-v*((point z).2-center.2))
  opposite_left : ∀ z, z∈selected ∨ z+1∈selected →
    affineEval (L (opposite z)) (point z)=0
  opposite_right : ∀ z, z∈selected ∨ z+1∈selected →
    affineEval (L (opposite z)) (point (z+1))=0
  opposite_avoids_center : ∀ z, z∈selected ∨ z+1∈selected →
    affineEval (L (opposite z)) center≠0
  triangle_nondegenerate : ∀ z, z∈selected ∨ z+1∈selected →
    areaDet center (point z) (point (z+1))≠0

namespace Geometry

/-- The geometric fan cannot have r-1 consecutive selected internal rays. -/
theorem no_long_run {n r : ℕ} [NeZero (2*r)] {L : ℕ → Line ℝ}
    (f : Geometry n r L) (hr : 3≤r) (base : ZMod (2*r)) :
    ∃ j : Fin (r-1), base+((j.val+1 : ℕ) : ZMod (2*r))∉f.selected := by
  classical
  by_contra hh
  push Not at hh
  have hmem (i : ℕ) (hi : 0 < i) (hir : i < r) :
      base+(i : ZMod (2*r))∈f.selected := by
    have he : i-1+1=i := by omega
    simpa only [he] using hh ⟨i-1,by omega⟩
  have hsector (j : ℕ) (hj : j < r) :
      base+(j : ZMod (2*r))∈f.selected ∨
      (base+(j : ZMod (2*r)))+1∈f.selected := by
    by_cases hzero : j=0
    · right
      subst j
      simpa using hmem 1 (by omega) (by omega)
    · left
      exact hmem j (by omega) hj
  let strip : FanStrip n r L := {
    center := f.center
    point := fun j => f.point (base+(j : ZMod (2*r)))
    radial := fun j => f.radial (base+(j : ZMod (2*r)))
    opposite := fun j => f.opposite (base+(j : ZMod (2*r)))
    positive_length := by omega
    radial_center := fun j _ => f.radial_center _
    radial_point := fun j _ => f.radial_point _
    opposite_left := fun j hj => f.opposite_left _ (hsector j hj)
    opposite_right := by
      intro j hj
      simpa only [Nat.cast_add,Nat.cast_one,add_assoc] using
        f.opposite_right _ (hsector j hj)
    opposite_avoids_center := fun j hj => f.opposite_avoids_center _ (hsector j hj)
    triangle_nondegenerate := by
      intro j hj
      simpa only [Nat.cast_add,Nat.cast_one,add_assoc] using
        f.triangle_nondegenerate _ (hsector j hj)
    ordinary_internal := fun j hj hjr => f.ordinary _ (hmem j hj hjr)
  }
  rcases f.antipodal base with ⟨v,hv,hanti⟩
  have hp : strip.point 0=
      (strip.center.1+1*((f.point base).1-f.center.1),
       strip.center.2+1*((f.point base).2-f.center.2)) := by
    dsimp [strip]
    simp
  have hbad := no_opposite_end_fan strip
    ((f.point base).1-f.center.1,(f.point base).2-f.center.2) 1 v
    (by norm_num) hv hp
  apply hbad
  simpa only [strip] using hanti

/-- Geometric local fan bound, with no combinatorial run premise left over. -/
theorem selected_card_le {n r : ℕ} [NeZero (2*r)] {L : ℕ → Line ℝ}
    (f : Geometry n r L) (hr : 3≤r) : f.selected.card≤2*r-3 := by
  apply FanCount.ordinary_shared_ray_bound r hr f.selected
  intro start
  rcases f.no_long_run hr (start-1) with ⟨j,hj⟩
  refine ⟨j,?_⟩
  have he : start-1+((j.val+1 : ℕ) : ZMod (2*r))=
      start+(j.val : ZMod (2*r)) := by
    push_cast
    ring
  simpa only [he] using hj

#print axioms no_long_run
#print axioms selected_card_le

end Geometry
end Kobon.CyclicFan
