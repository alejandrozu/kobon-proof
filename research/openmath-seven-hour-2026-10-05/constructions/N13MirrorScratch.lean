import Kobon.UpperOpenMathAntipodalFullNeighborPair

namespace Kobon.UpperOpenMathN13MirrorScratch
open Cells FanGeometry UpperFan UpperOpenMathAlignedTriangles Finset
set_option maxHeartbeats 1000000

/-- Reverse the cyclic indexing while retaining the actual triangle supports.
    Areas reverse sign; the points and indexed arrangement are unchanged. -/
noncomputable def mirror {n : ℕ} {L : ℕ → Line ℝ}
    (f : Sectors n 3 L) (a : ZMod 6) : Sectors n 3 L where
  center := f.center
  point := fun z=>f.point (a-z)
  radial := fun z=>f.radial (a-z)
  opposite := fun z=>f.opposite (a-z-1)
  triangular := f.triangular.preimage (fun z=>a-z-1) (by
    intro x _ y _ h
    have he : a-x=a-y := by
      simpa only [sub_add_cancel] using congrArg (fun q : ZMod 6=>q+1) h
    exact sub_right_injective he)
  triangle := fun z=>UpperOpenMathAlignedTriangles.reverse (f.triangle (a-z-1))
  radial_center := fun z=>f.radial_center (a-z)
  radial_point := fun z=>f.radial_point (a-z)
  antipodal := by
    intro z
    obtain ⟨v,hv,he⟩ := f.antipodal (a-z)
    refine ⟨v,hv,?_⟩
    have hi : a-(z+3)=(a-z)+3 := (by decide : ∀ a z : ZMod 6, a-(z+3)=(a-z)+3) a z
    simpa only [Nat.cast_ofNat,hi] using he
  triangle_center := by
    intro z hz
    exact f.triangle_center (a-z-1) ((mem_preimage (f := fun q : ZMod 6=>a-q-1)).mp hz)
  triangle_left := by
    intro z hz
    change (f.triangle (a-z-1)).r=f.point (a-z)
    have hi : a-z-1+1=a-z := by ring
    simpa only [hi] using f.triangle_right (a-z-1) ((mem_preimage (f := fun q : ZMod 6=>a-q-1)).mp hz)
  triangle_right := by
    intro z hz
    change (f.triangle (a-z-1)).q=f.point (a-(z+1))
    have hi : a-(z+1)=a-z-1 := by ring
    rw [hi]
    exact f.triangle_left (a-z-1) ((mem_preimage (f := fun q : ZMod 6=>a-q-1)).mp hz)
  triangle_support := by
    intro z hz
    exact f.triangle_support (a-z-1) ((mem_preimage (f := fun q : ZMod 6=>a-q-1)).mp hz)

@[simp] theorem mirror_center {n : ℕ} {L : ℕ → Line ℝ}
    (f : Sectors n 3 L) (a : ZMod 6) : (mirror f a).center=f.center := rfl
@[simp] theorem mirror_point {n : ℕ} {L : ℕ → Line ℝ}
    (f : Sectors n 3 L) (a z : ZMod 6) : (mirror f a).point z=f.point (a-z) := rfl
@[simp] theorem mirror_opposite {n : ℕ} {L : ℕ → Line ℝ}
    (f : Sectors n 3 L) (a z : ZMod 6) : (mirror f a).opposite z=f.opposite (a-z-1) := rfl
@[simp] theorem mirror_mem_triangular {n : ℕ} {L : ℕ → Line ℝ}
    (f : Sectors n 3 L) (a z : ZMod 6) : z∈(mirror f a).triangular ↔ a-z-1∈f.triangular := by
  classical
  simp [mirror]
@[simp] theorem mirror_mem_shared {n : ℕ} {L : ℕ → Line ℝ}
    (f : Sectors n 3 L) (a z : ZMod 6) : z∈(mirror f a).shared ↔ a-z∈f.shared := by
  classical
  simp only [Sectors.shared,mem_filter]
  change (z∈(mirror f a).triangular ∧ z-1∈(mirror f a).triangular) ↔
    (a-z∈f.triangular ∧ a-z-1∈f.triangular)
  rw [mirror_mem_triangular f a z,mirror_mem_triangular f a (z-1)]
  have hi : a-(z-1)-1=a-z := by ring
  rw [hi]
  exact and_comm
@[simp] theorem mirror_mem_ordinaryShared {n : ℕ} {L : ℕ → Line ℝ}
    (f : Sectors n 3 L) (a z : ZMod 6) : z∈(mirror f a).ordinaryShared ↔ a-z∈f.ordinaryShared := by
  classical
  simp only [Sectors.ordinaryShared,mem_filter,mirror_point]
  change (z∈(mirror f a).shared ∧ OrdinaryAt n L (f.point (a-z))) ↔
    (a-z∈f.shared ∧ OrdinaryAt n L (f.point (a-z)))
  rw [mirror_mem_shared f a z]
@[simp] theorem mirror_mem_coreShared {n : ℕ} {L : ℕ → Line ℝ}
    (f : Sectors n 3 L) (a z : ZMod 6) : z∈(mirror f a).coreShared ↔ a-z∈f.coreShared := by
  classical
  simp only [Sectors.coreShared,mem_sdiff]
  change (z∈(mirror f a).shared ∧ z∉(mirror f a).ordinaryShared) ↔
    (a-z∈f.shared ∧ a-z∉f.ordinaryShared)
  rw [mirror_mem_shared f a z,mirror_mem_ordinaryShared f a z]

theorem mirror_full {n : ℕ} {L : ℕ → Line ℝ}
    (f : Sectors n 3 L) (a : ZMod 6) (full : f.triangular=univ) :
    (mirror f a).triangular=univ := by
  classical
  ext z
  rw [mirror_mem_triangular f a z]
  simp [full]

theorem mirror_injective {n : ℕ} {L : ℕ → Line ℝ}
    (f : Sectors n 3 L) (a : ZMod 6) (inj : Function.Injective f.point) :
    Function.Injective (mirror f a).point := by
  intro x y h
  exact sub_right_injective (inj h)

theorem mirror_area {n : ℕ} {L : ℕ → Line ℝ}
    (f : Sectors n 3 L) (a z : ZMod 6) :
    areaDet (mirror f a).center ((mirror f a).point z) ((mirror f a).point (z+1))=
      -areaDet f.center (f.point (a-z-1)) (f.point (a-z)) := by
  have hi : a-(z+1)=a-z-1 := by ring
  simp only [mirror_center,mirror_point,hi]
  dsimp [areaDet]
  ring

#print axioms mirror
#print axioms mirror_area
end Kobon.UpperOpenMathN13MirrorScratch





