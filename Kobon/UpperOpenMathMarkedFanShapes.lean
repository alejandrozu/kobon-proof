import Kobon.UpperOpenMathTripleZeroCurvature
import Kobon.UpperOpenMathMarkedCurvatureWeights

/-! The actual geometric shapes forced by a marked full two-cap fan and
its zero-ordinary-degree target. The target continues antipodally, while
the source's opposite core port has nonordinary neighboring tips. -/
namespace Kobon.UpperOpenMathMarkedFanShapes
open Cells FanGeometry UpperFan UpperOpenMathTripleCharts Finset
set_option maxHeartbeats 1000000

theorem finite_marked_offsets : ∀ z : ZMod 6,
    z-1≠z+1 ∧ z+2≠z-1 ∧ z+2≠z+1 ∧ z+3≠z-1 ∧
      z+3≠z+1 ∧ z+4≠z-1 ∧ z+4≠z+1 := by decide +kernel

theorem full_two_cap_opposite_card {n r : ℕ} [NeZero (2*r)]
    {L : ℕ → Line ℝ} (hr : r=3) (f : UpperFan.Sectors n r L)
    (ao : f.ordinaryShared.card=2) (dc : f.coreShared.card=4)
    (z : ZMod (2*r)) (prev : z-1∈f.ordinaryShared)
    (next : z+1∈f.ordinaryShared) :
    z+3∈f.coreShared ∧
      ¬OrdinaryAt n L (f.point (z+2)) ∧ ¬OrdinaryAt n L (f.point (z+4)) := by
  classical
  subst r
  have off := finite_marked_offsets z
  have eqO : f.ordinaryShared={z-1,z+1} := by
    apply Eq.symm
    apply eq_of_subset_of_card_le
    · intro a ha
      rcases mem_insert.mp ha with rfl|ha
      · exact prev
      · simpa only [mem_singleton.mp ha] using next
    · rw [card_pair off.1,ao]
  have shcard : f.shared.card=6 := by have := f.shared_card_split; omega
  have allShared : f.shared=univ := by
    apply eq_of_subset_of_card_le (subset_univ _)
    simpa only [card_univ,ZMod.card] using shcard.ge
  have allTriangular : f.triangular=univ := by
    apply eq_of_subset_of_card_le (subset_univ _)
    have ss : f.shared⊆f.triangular := filter_subset _ _
    have ge := card_le_card ss
    simpa only [card_univ,ZMod.card] using (le_trans shcard.ge ge)
  have noO2 : z+2∉f.ordinaryShared := by rw [eqO]; simpa only [mem_insert,mem_singleton] using not_or.mpr ⟨off.2.1,off.2.2.1⟩
  have noO3 : z+3∉f.ordinaryShared := by rw [eqO]; simpa only [mem_insert,mem_singleton] using not_or.mpr ⟨off.2.2.2.1,off.2.2.2.2.1⟩
  have noO4 : z+4∉f.ordinaryShared := by rw [eqO]; simpa only [mem_insert,mem_singleton] using not_or.mpr ⟨off.2.2.2.2.2.1,off.2.2.2.2.2.2⟩
  have nonordinary (a : ZMod 6) (ha : a∉f.ordinaryShared) : ¬OrdinaryAt n L (f.point a) := by
    intro ho
    exact ha ((f.mem_ordinaryShared a).mpr ⟨by rw [allTriangular]; simp,by rw [allTriangular]; simp,ho⟩)
  exact ⟨mem_sdiff.mpr ⟨by rw [allShared]; simp,noO3⟩,nonordinary _ noO2,nonordinary _ noO4⟩

theorem poor_antipodal_core_card {n r : ℕ} [NeZero (2*r)]
    {L : ℕ → Line ℝ} (hr : r=3) (g : UpperFan.Sectors n r L)
    (ao : g.ordinaryShared.card=0) (dc : g.coreShared.card=2)
    (b : ZMod (2*r)) (bc : b∈g.coreShared)
    (op : OrdinaryAt n L (g.point (b-1)))
    (on : OrdinaryAt n L (g.point (b+1))) : b+3∈g.coreShared := by
  classical
  subst r
  let f := UpperOpenMathRotation.Sectors.shift g b
  have ordZero : f.ordinaryShared=∅ := card_eq_zero.mp (by
    rw [UpperOpenMathRotation.Sectors.shift_ordinaryShared_card]; exact ao)
  have corTwo : f.coreShared.card=2 := by rw [UpperOpenMathRotation.Sectors.shift_coreShared_card]; exact dc
  have h0 : (0 : ZMod 6)∈f.coreShared := by
    apply (UpperOpenMathRotation.Sectors.shift_mem_coreShared g b 0).mpr
    simpa only [add_zero] using bc
  have h5 : b+(5 : ZMod 6)=b-1 := by
    have he : (5 : ZMod 6)= -1 := by decide
    rw [he]; ring
  have op5 : OrdinaryAt n L (f.point 5) := by simpa only [f,UpperOpenMathRotation.Sectors.shift_point,h5] using op
  have on1 : OrdinaryAt n L (f.point 1) := on
  have hs := mem_filter.mp (mem_sdiff.mp h0).1
  have ht0 : (0 : ZMod 6)∈f.triangular := hs.1
  have ht5 : (5 : ZMod 6)∈f.triangular := by
    have he : (0 : ZMod 6)-1=5 := by decide
    simpa only [he] using hs.2
  have ht1 : (1 : ZMod 6)∉f.triangular := by
    intro h
    have ho : (1 : ZMod 6)∈f.ordinaryShared := (f.mem_ordinaryShared 1).mpr ⟨h,by simpa using ht0,on1⟩
    rw [ordZero] at ho
    exact notMem_empty _ ho
  have ht4 : (4 : ZMod 6)∉f.triangular := by
    intro h
    have ho : (5 : ZMod 6)∈f.ordinaryShared := (f.mem_ordinaryShared 5).mpr ⟨ht5,by simpa using h,op5⟩
    rw [ordZero] at ho
    exact notMem_empty _ ho
  have sub : f.coreShared⊆{0,3} := by
    intro z hz
    exact UpperOpenMathMarkedPoverty.finite_shared_subset f.triangular ht1 ht4 (mem_sdiff.mp hz).1
  have eqC : f.coreShared={0,3} := by
    apply eq_of_subset_of_card_le sub
    have cc : ({0,3} : Finset (ZMod 6)).card=2 := by decide
    rw [cc,corTwo]
  have h3 : (3 : ZMod 6)∈f.coreShared := by rw [eqC]; simp
  exact (UpperOpenMathRotation.Sectors.shift_mem_coreShared g b 3).mp h3

theorem normalized_nonordinary_neighbors_incompatible {α : Type*} [Fintype α]
    (G : α → TriangleGeometry)
    (disjoint : Pairwise (fun a b => Disjoint (G a).interior (G b).interior))
    {n r : ℕ} [NeZero (2*r)] {L : ℕ → Line ℝ} (hr : 2≤r)
    (f : UpperFan.Sectors n 3 L) (g : UpperFan.Sectors n r L)
    (df : NormalizedData G f)
    (ginj : Function.Injective g.point) (gnc : ∀ z, g.point z≠g.center)
    (gpos : ∀ z, 0<areaDet g.center (g.point z) (g.point (z+1)))
    (gactual : ∀ z∈g.triangular, Nonempty
      (UpperOpenMathSectorRecords.Occurrence G g.center g.point z))
    (z : ZMod (2*3)) (w : ZMod (2*r))
    (fz : z∈f.coreShared) (gw : w∈g.coreShared)
    (gc : g.center=f.point z) (gp : g.point w=f.center)
    (np : ¬OrdinaryAt n L (g.point (w-1)))
    (nn : ¬OrdinaryAt n L (g.point (w+1))) : False := by
  have fs := (mem_sdiff.mp fz).1
  have gs := (mem_sdiff.mp gw).1
  obtain ⟨fo⟩ := df.occurrences (z-1) (mem_filter.mp fs).2
  obtain ⟨fp⟩ := df.occurrences z (mem_filter.mp fs).1
  obtain ⟨go⟩ := gactual (w-1) (mem_filter.mp gs).2
  obtain ⟨gq⟩ := gactual w (mem_filter.mp gs).1
  have matching := UpperOpenMathFiberMatching.neighboring_points_match G disjoint
    (by decide : 2≤3) hr f.center g.center f.point g.point
    df.injective ginj df.noncentral gnc df.positive gpos z w gc gp fo fp go gq
  have cases : z=1 ∨ z=2 := by simpa only [df.core_eq,mem_insert,mem_singleton] using fz
  rcases cases with rfl|rfl
  · have ho : OrdinaryAt n L (f.point 0) :=
      ((f.mem_ordinaryShared 0).mp (by rw [df.ordinary_eq]; simp)).2.2
    have he : g.point (w+1)=f.point 0 := by simpa using matching.2
    exact nn (he.symm ▸ ho)
  · have ho : OrdinaryAt n L (f.point 3) :=
      ((f.mem_ordinaryShared 3).mp (by rw [df.ordinary_eq]; simp)).2.2
    have he : g.point (w-1)=f.point 3 := by
      have hx : (2 : ZMod (2*3))+1=3 := by decide
      simpa only [hx] using matching.1
    exact np (he.symm ▸ ho)

#print axioms full_two_cap_opposite_card
#print axioms poor_antipodal_core_card
#print axioms normalized_nonordinary_neighbors_incompatible
end Kobon.UpperOpenMathMarkedFanShapes
