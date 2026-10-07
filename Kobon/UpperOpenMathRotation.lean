import Kobon.UpperTripleFan

/-!
# Cyclic transport of actual geometric sector fans

Reindexing by a cyclic translation preserves every geometric field, the
ordinary/core shared-ray counts, and positive orientation. The local
incompatibility of extremal triple fans therefore applies to any matched
incident rays, without assuming that their indices are already zero.

The matching equations remain explicit geometric premises: this module does
not assert that whole-arrangement fan extraction has already been completed.
-/
namespace Kobon.UpperOpenMathRotation
open Cells FanGeometry UpperFan Finset

namespace Sectors
variable {n r : ℕ} [NeZero (2*r)] {L : ℕ → Line ℝ}

noncomputable def shift (f : UpperFan.Sectors n r L) (a : ZMod (2*r)) :
    UpperFan.Sectors n r L where
  center := f.center
  point := fun z => f.point (a+z)
  radial := fun z => f.radial (a+z)
  opposite := fun z => f.opposite (a+z)
  triangular := f.triangular.preimage (fun z => a+z) (by
    intro x _ y _ h; exact add_left_cancel h)
  triangle := fun z => f.triangle (a+z)
  radial_center := fun z => f.radial_center (a+z)
  radial_point := fun z => f.radial_point (a+z)
  antipodal := by
    intro z
    simpa only [← add_assoc] using f.antipodal (a+z)
  triangle_center := by
    intro z hz
    exact f.triangle_center (a+z) (mem_preimage.mp hz)
  triangle_left := by
    intro z hz
    exact f.triangle_left (a+z) (mem_preimage.mp hz)
  triangle_right := by
    intro z hz
    simpa only [add_assoc] using f.triangle_right (a+z) (mem_preimage.mp hz)
  triangle_support := by
    intro z hz
    exact f.triangle_support (a+z) (mem_preimage.mp hz)

@[simp] theorem shift_center (f : UpperFan.Sectors n r L) (a : ZMod (2*r)) :
    (shift f a).center=f.center := rfl

@[simp] theorem shift_point (f : UpperFan.Sectors n r L) (a z : ZMod (2*r)) :
    (shift f a).point z=f.point (a+z) := rfl

@[simp] theorem shift_mem_triangular (f : UpperFan.Sectors n r L)
    (a z : ZMod (2*r)) : z∈(shift f a).triangular ↔ a+z∈f.triangular := by
  classical
  simp [shift]

@[simp] theorem shift_mem_shared (f : UpperFan.Sectors n r L)
    (a z : ZMod (2*r)) : z∈(shift f a).shared ↔ a+z∈f.shared := by
  classical
  simp only [UpperFan.Sectors.shared,mem_filter,shift_mem_triangular]
  have he : a+(z-1)=a+z-1 := by ring
  rw [he]

@[simp] theorem shift_mem_ordinaryShared (f : UpperFan.Sectors n r L)
    (a z : ZMod (2*r)) : z∈(shift f a).ordinaryShared ↔ a+z∈f.ordinaryShared := by
  classical
  simp only [UpperFan.Sectors.ordinaryShared,mem_filter,shift_mem_shared,shift_point]

@[simp] theorem shift_mem_coreShared (f : UpperFan.Sectors n r L)
    (a z : ZMod (2*r)) : z∈(shift f a).coreShared ↔ a+z∈f.coreShared := by
  classical
  simp only [UpperFan.Sectors.coreShared,mem_sdiff,shift_mem_shared,
    shift_mem_ordinaryShared]

theorem shift_ordinaryShared_card (f : UpperFan.Sectors n r L)
    (a : ZMod (2*r)) : (shift f a).ordinaryShared.card=f.ordinaryShared.card := by
  classical
  have he : (shift f a).ordinaryShared.image (fun z => a+z)=f.ordinaryShared := by
    ext z
    constructor
    · rintro hz
      obtain ⟨x,hx,rfl⟩ := mem_image.mp hz
      exact (shift_mem_ordinaryShared f a x).mp hx
    · intro hz
      exact mem_image.mpr ⟨z-a,by simpa using hz,by ring⟩
  rw [← he,card_image_of_injective _ (by
    intro x y h; exact add_left_cancel h)]

theorem shift_coreShared_card (f : UpperFan.Sectors n r L)
    (a : ZMod (2*r)) : (shift f a).coreShared.card=f.coreShared.card := by
  classical
  have he : (shift f a).coreShared.image (fun z => a+z)=f.coreShared := by
    ext z
    constructor
    · rintro hz
      obtain ⟨x,hx,rfl⟩ := mem_image.mp hz
      exact (shift_mem_coreShared f a x).mp hx
    · intro hz
      exact mem_image.mpr ⟨z-a,by simpa using hz,by ring⟩
  rw [← he,card_image_of_injective _ (by
    intro x y h; exact add_left_cancel h)]

theorem shift_positive (f : UpperFan.Sectors n r L)
    (positive : ∀ z, 0<areaDet f.center (f.point z) (f.point (z+1)))
    (a : ZMod (2*r)) :
    ∀ z, 0<areaDet (shift f a).center ((shift f a).point z)
      ((shift f a).point (z+1)) := by
  intro z
  simpa only [shift_center,shift_point,add_assoc] using positive (a+z)

end Sectors

/-- The shared ray may have any cyclic index in each fan. The endpoint
matches encode the same two triangles incident to the common edge. -/
theorem extremal_triple_fans_not_adjacent_at {n : ℕ} {L : ℕ → Line ℝ}
    (hL : NoParallel n L) (f g : UpperFan.Sectors n 3 L)
    (a b : ZMod 6) (hf : 3≤f.ordinaryShared.card) (hg : 3≤g.ordinaryShared.card)
    (fcore : a∉f.ordinaryShared) (gcore : b∉g.ordinaryShared)
    (centerg : g.center=f.point a) (pointg : g.point b=f.center)
    (rightg : g.point (b-1)=f.point (a+1))
    (leftg : g.point (b+1)=f.point (a-1))
    (positive : ∀ z, 0<areaDet f.center (f.point z) (f.point (z+1))) : False := by
  apply UpperTripleFan.extremal_triple_fans_not_adjacent hL
    (Sectors.shift f a) (Sectors.shift g b)
  · simpa only [Sectors.shift_ordinaryShared_card] using hf
  · simpa only [Sectors.shift_ordinaryShared_card] using hg
  · intro h
    apply fcore
    simpa only [add_zero] using (Sectors.shift_mem_ordinaryShared f a 0).mp h
  · intro h
    apply gcore
    simpa only [add_zero] using (Sectors.shift_mem_ordinaryShared g b 0).mp h
  · simpa using centerg
  · simpa using pointg
  · have he : b+(5 : ZMod 6)=b-1 := by
      have hh : (5 : ZMod 6)= -1 := by decide
      rw [hh]; ring
    simpa only [Sectors.shift_point,he] using rightg
  · have he : a+(5 : ZMod 6)=a-1 := by
      have hh : (5 : ZMod 6)= -1 := by decide
      rw [hh]; ring
    simpa only [Sectors.shift_point,he] using leftg
  · exact Sectors.shift_positive f positive a

#print axioms Sectors.shift_ordinaryShared_card
#print axioms Sectors.shift_coreShared_card
#print axioms extremal_triple_fans_not_adjacent_at
end Kobon.UpperOpenMathRotation
