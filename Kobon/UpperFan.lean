import Kobon.CyclicFan
import Mathlib.Data.Finset.Card

/-!
# A sharper local shared-ray bound

This file strengthens the local cyclic fan estimate.  A pair of consecutive
unselected rays forces at least four unselected rays in total.  Consequently,
the extremal ordinary-ray count can occur only when every sector is triangular
and there are exactly three shared rays with nonordinary other endpoints.

The theorems concern explicit cyclic data of real triangles.  Extracting those
data and the global elementary-edge budget from an arbitrary arrangement is a
separate obligation; no unrestricted global Kobon upper theorem is asserted.
-/

namespace Kobon.UpperFan
open Finset

private theorem offset_ne {r a b : ℕ} [NeZero (2*r)]
    (base : ZMod (2*r)) (ha : a<2*r) (hb : b<2*r) (hab : a≠b) :
    base+(a : ZMod (2*r))≠base+(b : ZMod (2*r)) := by
  intro he
  have hc : (a : ZMod (2*r))=(b : ZMod (2*r)) := add_left_cancel he
  have hv := congrArg ZMod.val hc
  rw [ZMod.val_natCast_of_lt ha,ZMod.val_natCast_of_lt hb] at hv
  exact hab hv

/-- Two consecutive omitted rays, together with the geometric no-long-run
condition, force four omissions rather than the usual three. -/
theorem card_le_of_adjacent_missing (r : ℕ) (hr : 3≤r)
    (S : Finset (ZMod (2*r)))
    (no_run : ∀ start : ZMod (2*r), ∃ j : Fin (r-1),
      start+(j.val : ZMod (2*r))∉S)
    (base : ZMod (2*r)) (hbase : base∉S) (hnext : base+1∉S) :
    S.card≤2*r-4 := by
  classical
  letI : NeZero (2*r) := ⟨by omega⟩
  obtain ⟨j,hj⟩ := no_run (base+2)
  obtain ⟨k,hk⟩ := no_run (base+((r+1 : ℕ) : ZMod (2*r)))
  let x := 2+j.val
  let y := r+1+k.val
  have hx : 2≤x ∧ x≤r := by dsimp [x]; have := j.isLt; omega
  have hy : r+1≤y ∧ y<2*r := by dsimp [y]; have := k.isLt; omega
  have hxmem : base+(x : ZMod (2*r))∉S := by
    simpa only [x,Nat.cast_add,Nat.cast_ofNat,add_assoc] using hj
  have hymem : base+(y : ZMod (2*r))∉S := by
    simpa only [y,Nat.cast_add,Nat.cast_one,add_assoc] using hk
  have h01 : base≠base+1 := by
    simpa using offset_ne base (a:=0) (b:=1) (by omega) (by omega) (by omega)
  have h0x : base≠base+(x : ZMod (2*r)) := by
    simpa using offset_ne base (a:=0) (b:=x) (by omega) (by omega) (by omega)
  have h0y : base≠base+(y : ZMod (2*r)) := by
    simpa using offset_ne base (a:=0) (b:=y) (by omega) hy.2 (by omega)
  have h1x : base+1≠base+(x : ZMod (2*r)) := by
    simpa using offset_ne base (a:=1) (b:=x) (by omega) (by omega) (by omega)
  have h1y : base+1≠base+(y : ZMod (2*r)) := by
    simpa using offset_ne base (a:=1) (b:=y) (by omega) hy.2 (by omega)
  have hxy : base+(x : ZMod (2*r))≠base+(y : ZMod (2*r)) :=
    offset_ne base (by omega) hy.2 (by omega)
  let omitted : Finset (ZMod (2*r)) :=
    {base,base+1,base+(x : ZMod (2*r)),base+(y : ZMod (2*r))}
  have hc : omitted.card=4 := by simp [omitted,h01,h0x,h0y,h1x,h1y,hxy]
  have hsub : omitted⊆univ\S := by
    intro z hz
    simp only [omitted,mem_insert,mem_singleton] at hz
    rcases hz with rfl|rfl|rfl|rfl <;> simp [hbase,hnext,hxmem,hymem]
  have hle := card_le_card hsub
  have htotal := card_sdiff_add_card_eq_card (subset_univ S)
  rw [hc] at hle
  simp only [card_univ,ZMod.card] at htotal
  omega

section Geometry
open FanGeometry

/-- A cyclic family of actual real triangular sectors at a multiple point.
Only the sectors in `triangular` are asserted triangular. A radial side is
shared when both neighboring sectors are triangular; ordinary shared sides
are selected by the actual line-incidence predicate `OrdinaryAt`.

This is a local interface, not an assertion that its data have already been
extracted from every finite arrangement. -/
structure Sectors (n r : ℕ) [NeZero (2*r)] (L : ℕ → Line ℝ) where
  center : Point
  point : ZMod (2*r) → Point
  radial : ZMod (2*r) → Fin n
  opposite : ZMod (2*r) → Fin n
  triangular : Finset (ZMod (2*r))
  triangle : ZMod (2*r) → Cells.TriangleGeometry
  radial_center : ∀ z, affineEval (L (radial z)) center=0
  radial_point : ∀ z, affineEval (L (radial z)) (point z)=0
  antipodal : ∀ z, ∃ v : ℝ, 0<v ∧
    point (z+(r : ZMod (2*r)))=
      (center.1-v*((point z).1-center.1),center.2-v*((point z).2-center.2))
  triangle_center : ∀ z, z∈triangular → (triangle z).p=center
  triangle_left : ∀ z, z∈triangular → (triangle z).q=point z
  triangle_right : ∀ z, z∈triangular → (triangle z).r=point (z+1)
  triangle_support : ∀ z, z∈triangular → (triangle z).A=L (opposite z)

namespace Sectors
variable {n r : ℕ} [NeZero (2*r)] {L : ℕ → Line ℝ} (f : Sectors n r L)

def shared : Finset (ZMod (2*r)) := f.triangular.filter (fun z => z-1∈f.triangular)

noncomputable def ordinaryShared : Finset (ZMod (2*r)) := by
  classical
  exact f.shared.filter (fun z => OrdinaryAt n L (f.point z))

noncomputable def coreShared : Finset (ZMod (2*r)) := f.shared\f.ordinaryShared

theorem mem_ordinaryShared (z : ZMod (2*r)) :
    z∈f.ordinaryShared ↔ z∈f.triangular ∧ z-1∈f.triangular ∧
      OrdinaryAt n L (f.point z) := by
  classical
  simp [ordinaryShared,shared,and_assoc]

theorem ordinaryShared_subset : f.ordinaryShared⊆f.shared := by
  classical
  exact filter_subset _ _

theorem sector_of_adjacent_selected (z : ZMod (2*r))
    (hz : z∈f.ordinaryShared ∨ z+1∈f.ordinaryShared) : z∈f.triangular := by
  rcases hz with hz|hz
  · exact ((f.mem_ordinaryShared z).mp hz).1
  · have hh := ((f.mem_ordinaryShared (z+1)).mp hz).2.1
    simpa using hh

/-- The no-long-run geometric interface is derived from actual triangles. -/
noncomputable def asCyclic : CyclicFan.Geometry n r L where
  center := f.center
  point := f.point
  radial := f.radial
  opposite := f.opposite
  selected := f.ordinaryShared
  radial_center := f.radial_center
  radial_point := f.radial_point
  ordinary := fun z hz => ((f.mem_ordinaryShared z).mp hz).2.2
  antipodal := f.antipodal
  opposite_left := by
    intro z hz
    have ht := f.sector_of_adjacent_selected z hz
    simpa only [f.triangle_support z ht,f.triangle_left z ht] using (f.triangle z).Aq
  opposite_right := by
    intro z hz
    have ht := f.sector_of_adjacent_selected z hz
    simpa only [f.triangle_support z ht,f.triangle_right z ht] using (f.triangle z).Ar
  opposite_avoids_center := by
    intro z hz
    have ht := f.sector_of_adjacent_selected z hz
    simpa only [f.triangle_support z ht,f.triangle_center z ht] using (f.triangle z).Ap
  triangle_nondegenerate := by
    intro z hz
    have ht := f.sector_of_adjacent_selected z hz
    simpa only [f.triangle_center z ht,f.triangle_left z ht,f.triangle_right z ht]
      using (f.triangle z).nondegenerate

theorem no_run (hr : 3≤r) (start : ZMod (2*r)) :
    ∃ j : Fin (r-1), start+(j.val : ZMod (2*r))∉f.ordinaryShared := by
  obtain ⟨j,hj⟩ := f.asCyclic.no_long_run hr (start-1)
  refine ⟨j,?_⟩
  have he : start-1+((j.val+1 : ℕ) : ZMod (2*r))=
      start+(j.val : ZMod (2*r)) := by push_cast; ring
  simpa only [asCyclic,he] using hj

theorem ordinary_shared_card_le (hr : 3≤r) : f.ordinaryShared.card≤2*r-3 :=
  f.asCyclic.selected_card_le hr

/-- A missing triangular sector excludes both adjacent rays. At the maximal
ordinary shared-ray count this is impossible: it would force four omissions. -/
theorem all_sectors_of_extremal (hr : 3≤r)
    (hcard : 2*r-3≤f.ordinaryShared.card) : f.triangular=univ := by
  classical
  apply eq_univ_of_forall
  intro z
  by_contra hz
  have h0 : z∉f.ordinaryShared := fun h => hz ((f.mem_ordinaryShared z).mp h).1
  have h1 : z+1∉f.ordinaryShared := by
    intro h
    apply hz
    simpa using ((f.mem_ordinaryShared (z+1)).mp h).2.1
  have hb := card_le_of_adjacent_missing r hr f.ordinaryShared (f.no_run hr) z h0 h1
  omega

/-- Equality in the old 2r-3 bound forces exactly three shared rays with
nonordinary other endpoints. In particular, two such rays do not suffice. -/
theorem core_shared_card_eq_three_of_extremal (hr : 3≤r)
    (hcard : 2*r-3≤f.ordinaryShared.card) : f.coreShared.card=3 := by
  classical
  have hall := f.all_sectors_of_extremal hr hcard
  have hs : f.shared=univ := by simp [shared,hall]
  have ht := card_sdiff_add_card_eq_card f.ordinaryShared_subset
  have hb := f.ordinary_shared_card_le hr
  change f.coreShared.card+f.ordinaryShared.card=f.shared.card at ht
  rw [hs] at ht
  simp only [card_univ,ZMod.card] at ht
  omega

/-- Sharper real-sector bound: at most two core-ended shared rays imply at
most 2r-4 ordinary-ended shared rays. This strengthens the <=1 hypothesis
in the previous manuscript-level local refinement. -/
theorem ordinary_shared_card_le_of_core_le_two (hr : 3≤r)
    (hc : f.coreShared.card≤2) : f.ordinaryShared.card≤2*r-4 := by
  by_contra h
  have he := f.core_shared_card_eq_three_of_extremal hr (by omega)
  omega

/-- Except when exactly three core-ended shared rays occur, the improved
2r-4 estimate holds. -/
theorem ordinary_shared_card_le_of_core_ne_three (hr : 3≤r)
    (hc : f.coreShared.card≠3) : f.ordinaryShared.card≤2*r-4 := by
  by_contra h
  exact hc (f.core_shared_card_eq_three_of_extremal hr (by omega))

theorem shared_card_split : f.ordinaryShared.card+f.coreShared.card=f.shared.card := by
  classical
  rw [Nat.add_comm]
  exact card_sdiff_add_card_eq_card f.ordinaryShared_subset

theorem shared_card_le : f.ordinaryShared.card+f.coreShared.card≤2*r := by
  rw [f.shared_card_split]
  simpa only [card_univ,ZMod.card] using card_le_card (subset_univ f.shared)

/-- The weighted local inequality gains two units unless the local ordinary
shared count is extremal. Equality cases of that old bound have already been
shown to have a complete triangular fan and exactly three core-ended rays. -/
theorem weighted_local_bound (hr : 3≤r) :
    3*f.ordinaryShared.card+f.coreShared.card ≤
      6*r-8+(if f.ordinaryShared.card=2*r-3 then 2 else 0) := by
  have hb := f.ordinary_shared_card_le hr
  have ht := f.shared_card_le
  split
  · rename_i he
    have hc := f.core_shared_card_eq_three_of_extremal hr (by omega)
    omega
  · rename_i he
    omega

/-- If at most two shared sides end at another multiple point, the sharper
weighted inequality has no exceptional term. -/
theorem weighted_local_bound_of_core_le_two (hr : 3≤r)
    (hc : f.coreShared.card≤2) :
    3*f.ordinaryShared.card+f.coreShared.card≤6*r-8 := by
  have hb := f.ordinary_shared_card_le_of_core_le_two hr hc
  have ht := f.shared_card_le
  omega

end Sectors
end Geometry

#print axioms card_le_of_adjacent_missing
#print axioms Sectors.all_sectors_of_extremal
#print axioms Sectors.core_shared_card_eq_three_of_extremal
#print axioms Sectors.ordinary_shared_card_le_of_core_le_two
#print axioms Sectors.weighted_local_bound

end Kobon.UpperFan
