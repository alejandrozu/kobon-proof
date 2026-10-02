import Kobon.UpperFan
import Mathlib.Data.Finset.Max

/-!
# Extremal full fans cannot occur at exposed core points

The additional orientation hypothesis is the positive cyclic ordering of the
actual radial sectors. At every ordinary outer endpoint, the two opposite
supports coincide. A finite minimum principle then shows that a full fan's
nonordinary outer endpoints cannot all lie in one closed half-plane through
the center. For an extremal fan there are exactly three such shared endpoints.

This is local real geometry. Extracting consistently oriented sector data
from all cells of an arrangement and counting global core vertices remain
separate interfaces, not hidden conclusions of this module.
-/
namespace Kobon.UpperFanSupport
open Cells FanGeometry UpperFan Finset

theorem collinear_of_incident_line (l : Line ℝ) (c u p v : Point)
    (hc : affineEval l c≠0)
    (hu : affineEval l u=0) (hp : affineEval l p=0) (hv : affineEval l v=0) :
    areaDet u p v=0 := by
  by_contra h
  obtain ⟨ha,hb⟩ := three_zeros_force_zero_normal l u p v h hu hp hv
  apply hc
  simpa only [affineEval,ha,hb,zero_mul,zero_add] using hp

/-- A determinant identity for affine evaluations, before using collinearity. -/
theorem affine_area_identity (w : Line ℝ) (c u p v : Point) :
    areaDet c p v*(affineEval w u-affineEval w p)+
      areaDet c u p*(affineEval w v-affineEval w p)=
      areaDet u p v*(affineEval w c-affineEval w p) := by
  dsimp [areaDet,affineEval]
  ring

namespace Sectors
variable {n r : ℕ} [NeZero (2*r)] {L : ℕ → Line ℝ}
  (f : UpperFan.Sectors n r L)

theorem collinear_at_ordinary (hall : f.triangular=univ)
    (z : ZMod (2*r)) (ho : OrdinaryAt n L (f.point z)) :
    areaDet (f.point (z-1)) (f.point z) (f.point (z+1))=0 := by
  have hz : z∈f.ordinaryShared := by
    rw [f.mem_ordinaryShared]
    simp only [hall,mem_univ,true_and]
    exact ho
  have hprev : z-1∈f.ordinaryShared ∨ z-1+1∈f.ordinaryShared := by
    right
    simpa using hz
  have hcur : z∈f.ordinaryShared ∨ z+1∈f.ordinaryShared := Or.inl hz
  have he : f.opposite (z-1)=f.opposite z := by
    apply ordinary_nonradial_unique n L (f.point z) ho (f.radial z)
    · exact f.radial_point z
    · simpa [UpperFan.Sectors.asCyclic] using f.asCyclic.opposite_right (z-1) hprev
    · exact f.asCyclic.opposite_left z hcur
    · intro h
      have hh := f.radial_center z
      rw [← h] at hh
      exact f.asCyclic.opposite_avoids_center (z-1) hprev hh
    · intro h
      have hh := f.radial_center z
      rw [← h] at hh
      exact f.asCyclic.opposite_avoids_center z hcur hh
  apply collinear_of_incident_line (L (f.opposite z)) f.center
  · exact f.asCyclic.opposite_avoids_center z hcur
  · rw [← he]
    exact f.asCyclic.opposite_left (z-1) hprev
  · exact f.asCyclic.opposite_left z hcur
  · exact f.asCyclic.opposite_right z hcur

/-- A minimum of an affine functional propagates through an ordinary outer
endpoint when the two neighboring triangular sectors have positive orientation. -/
theorem next_eq_of_minimum (hall : f.triangular=univ)
    (positive : ∀ z, 0<areaDet f.center (f.point z) (f.point (z+1)))
    (w : Line ℝ) (z : ZMod (2*r)) (ho : OrdinaryAt n L (f.point z))
    (hp : affineEval w (f.point z)≤affineEval w (f.point (z-1)))
    (hn : affineEval w (f.point z)≤affineEval w (f.point (z+1))) :
    affineEval w (f.point (z+1))=affineEval w (f.point z) := by
  have hcol := collinear_at_ordinary f hall z ho
  have hleft : 0<areaDet f.center (f.point (z-1)) (f.point z) := by
    simpa using positive (z-1)
  have hright := positive z
  have hid := affine_area_identity w f.center (f.point (z-1))
    (f.point z) (f.point (z+1))
  rw [hcol,zero_mul] at hid
  have hnonneg := mul_nonneg hright.le (sub_nonneg.mpr hp)
  have hnonneg' := mul_nonneg hleft.le (sub_nonneg.mpr hn)
  have he : areaDet f.center (f.point (z-1)) (f.point z)*
      (affineEval w (f.point (z+1))-affineEval w (f.point z))=0 := by
    linarith
  exact sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_left hleft.ne')

/-- Finite minimum principle for a full oriented fan. If every nonordinary
outer endpoint lies on the nonnegative side of a line through the center,
then every outer endpoint does. -/
theorem nonnegative_of_core_nonnegative (hall : f.triangular=univ)
    (positive : ∀ z, 0<areaDet f.center (f.point z) (f.point (z+1)))
    (w : Line ℝ) (hw : affineEval w f.center=0)
    (hcore : ∀ z, ¬OrdinaryAt n L (f.point z) → 0≤affineEval w (f.point z)) :
    ∀ z, 0≤affineEval w (f.point z) := by
  classical
  obtain ⟨a,_,hmin⟩ := exists_min_image (univ : Finset (ZMod (2*r)))
    (fun z => affineEval w (f.point z)) (by simp)
  have hleast (z : ZMod (2*r)) :
      affineEval w (f.point a)≤affineEval w (f.point z) := hmin z (mem_univ z)
  by_contra hh
  push Not at hh
  obtain ⟨z,hz⟩ := hh
  have hnegative : affineEval w (f.point a)<0 := lt_of_le_of_lt (hleast z) hz
  have step (z : ZMod (2*r))
      (he : affineEval w (f.point z)=affineEval w (f.point a)) :
      affineEval w (f.point (z+1))=affineEval w (f.point a) := by
    have ho : OrdinaryAt n L (f.point z) := by
      by_contra ho
      have hc := hcore z ho
      rw [he] at hc
      linarith
    exact (next_eq_of_minimum f hall positive w z ho
      (by rw [he]; exact hleast (z-1))
      (by rw [he]; exact hleast (z+1))).trans he
  have iterated (k : ℕ) :
      affineEval w (f.point (a+(k : ZMod (2*r))))=affineEval w (f.point a) := by
    induction k with
    | zero => simp
    | succ k ih =>
      simpa only [Nat.cast_add,Nat.cast_one,add_assoc] using step (a+(k : ZMod (2*r))) ih
  obtain ⟨v,hv,he⟩ := f.antipodal a
  have hanti : affineEval w (f.point (a+(r : ZMod (2*r))))=
      (1+v)*affineEval w f.center-v*affineEval w (f.point a) := by
    rw [he]
    dsimp [affineEval]
    ring
  rw [iterated r,hw] at hanti
  have hp : 0<(1+v) := by linarith
  have hezero : (1+v)*affineEval w (f.point a)=0 := by nlinarith
  have ha := (mul_eq_zero.mp hezero).resolve_left hp.ne'
  linarith

/-- The nonordinary outer endpoints of a full positively oriented fan meet
both open sides of every valid line through its center. -/
theorem exists_negative_core_endpoint (hall : f.triangular=univ)
    (positive : ∀ z, 0<areaDet f.center (f.point z) (f.point (z+1)))
    (w : Line ℝ) (hw : affineEval w f.center=0) (valid : w.a≠0 ∨ w.b≠0) :
    ∃ z, ¬OrdinaryAt n L (f.point z) ∧ affineEval w (f.point z)<0 := by
  classical
  by_contra hh
  push Not at hh
  have hnonneg := nonnegative_of_core_nonnegative f hall positive w hw hh
  have hzero (z : ZMod (2*r)) : affineEval w (f.point z)=0 := by
    obtain ⟨v,hv,he⟩ := f.antipodal z
    have hanti : affineEval w (f.point (z+(r : ZMod (2*r))))=
        (1+v)*affineEval w f.center-v*affineEval w (f.point z) := by
      rw [he]
      dsimp [affineEval]
      ring
    rw [hw] at hanti
    have hn := hnonneg (z+(r : ZMod (2*r)))
    have hz := hnonneg z
    nlinarith
  have harea : areaDet f.center (f.point 0) (f.point 1)≠0 := by
    simpa using (positive 0).ne'
  obtain ⟨ha,hb⟩ := three_zeros_force_zero_normal w f.center (f.point 0) (f.point 1)
    harea hw (hzero 0) (hzero 1)
  rcases valid with ha'|hb'
  · exact ha' ha
  · exact hb' hb

/-- At an extremal ordinary-ray fan, the three core-ended shared endpoints
cannot lie in any one closed half-plane through the center. -/
theorem extremal_core_not_in_halfplane (hr : 3≤r)
    (hcard : 2*r-3≤f.ordinaryShared.card)
    (positive : ∀ z, 0<areaDet f.center (f.point z) (f.point (z+1)))
    (w : Line ℝ) (hw : affineEval w f.center=0) (valid : w.a≠0 ∨ w.b≠0) :
    ∃ z∈f.coreShared, affineEval w (f.point z)<0 := by
  classical
  have hall := f.all_sectors_of_extremal hr hcard
  obtain ⟨z,ho,hz⟩ := exists_negative_core_endpoint f hall positive w hw valid
  refine ⟨z,?_,hz⟩
  simp only [UpperFan.Sectors.coreShared,mem_sdiff]
  constructor
  · simp [UpperFan.Sectors.shared,hall]
  · intro hm
    exact ho ((f.mem_ordinaryShared z).mp hm).2.2

end Sectors

#print axioms Sectors.nonnegative_of_core_nonnegative
#print axioms Sectors.exists_negative_core_endpoint
#print axioms Sectors.extremal_core_not_in_halfplane
end Kobon.UpperFanSupport

