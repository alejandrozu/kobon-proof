import Kobon.UpperOpenMathMarkedFanShapes

/-! Two adjacent normalized two-cap triple cores cannot close their common
core triangle at a full third triple fan. No ordinary-cap hypothesis is
imposed at the third fan. -/
namespace Kobon.UpperOpenMathNormalizedPairFull
open Cells FanGeometry UpperFan UpperOpenMathTripleCharts
  UpperOpenMathTwoTwoCore Finset
set_option maxHeartbeats 1000000

theorem retained_matching_general {α : Type*} [Fintype α]
    (G : α → TriangleGeometry)
    (disjoint : Pairwise (fun a b => Disjoint (G a).interior (G b).interior))
    {n r : ℕ} [NeZero (2*r)] {L : ℕ → Line ℝ} (hr : 2≤r)
    (f : UpperFan.Sectors n 3 L) (k : UpperFan.Sectors n r L)
    (df : ChartData G f)
    (kinj : Function.Injective k.point) (knc : ∀ z, k.point z≠k.center)
    (kpos : ∀ z, 0<areaDet k.center (k.point z) (k.point (z+1)))
    (kactual : ∀ z∈k.triangular, Nonempty
      (UpperOpenMathSectorRecords.Occurrence G k.center k.point z))
    (z : ZMod (2*3)) (x : ZMod (2*r))
    (fz : z∈f.coreShared) (kx : x∈k.coreShared)
    (kc : k.center=f.point z) (kp : k.point x=f.center) :
    k.point (x-1)=f.point (z+1) ∧ k.point (x+1)=f.point (z-1) := by
  have fs := (mem_sdiff.mp fz).1
  have ks := (mem_sdiff.mp kx).1
  obtain ⟨fo⟩ := df.occurrences (z-1) (mem_filter.mp fs).2
  obtain ⟨fp⟩ := df.occurrences z (mem_filter.mp fs).1
  obtain ⟨ko⟩ := kactual (x-1) (mem_filter.mp ks).2
  obtain ⟨kq⟩ := kactual x (mem_filter.mp ks).1
  exact UpperOpenMathFiberMatching.neighboring_points_match G disjoint
    (by decide : 2≤3) hr f.center k.center f.point k.point
    df.injective kinj df.noncentral knc df.positive kpos z x kc kp fo fp ko kq

theorem normalized_pair_full_third_impossible {α : Type*} [Fintype α]
    (G : α → TriangleGeometry)
    (disjoint : Pairwise (fun a b => Disjoint (G a).interior (G b).interior))
    {n : ℕ} {L : ℕ → Line ℝ} (hL : NoParallel n L)
    (f g k : UpperFan.Sectors n 3 L) (df : NormalizedData G f) (dg : NormalizedData G g)
    (kinj : Function.Injective k.point) (knc : ∀ z, k.point z≠k.center)
    (kpos : ∀ z, 0<areaDet k.center (k.point z) (k.point (z+1)))
    (kactual : ∀ z∈k.triangular, Nonempty
      (UpperOpenMathSectorRecords.Occurrence G k.center k.point z))
    (kfull : k.triangular=univ)
    (w x : ZMod (2*3)) (gw : w∈g.coreShared) (kx : x∈k.coreShared)
    (gc : g.center=f.point 1) (gp : g.point w=f.center)
    (kc : k.center=f.point 2) (kp : k.point x=f.center) : False := by
  classical
  have h11 : (1 : ZMod (2*3))-1=0 := by decide
  have h12 : (1 : ZMod (2*3))+1=2 := by decide
  have h21 : (2 : ZMod (2*3))-1=1 := by decide
  have h23 : (2 : ZMod (2*3))+1=3 := by decide
  have f1 : (1 : ZMod (2*3))∈f.coreShared := by rw [df.core_eq]; simp
  have f2 : (2 : ZMod (2*3))∈f.coreShared := by rw [df.core_eq]; simp
  have g1 : (1 : ZMod (2*3))∈g.coreShared := by rw [dg.core_eq]; simp
  have ftip2no : ¬OrdinaryAt n L (f.point 2) := (mem_filter.mp (df.core_endpoint 2 f2)).2
  have gcenterNo : ¬OrdinaryAt n L g.center := by
    rw [gc]
    exact (mem_filter.mp (df.core_endpoint 1 f1)).2
  have fg := retained_neighbor_matching G disjoint f g df.toChartData dg.toChartData 1 w f1 gw gc gp
  have wtwo : w=2 := by
    have cases : w=1 ∨ w=2 := by simpa only [dg.core_eq,mem_insert,mem_singleton] using gw
    rcases cases with hw|hw
    · have go : OrdinaryAt n L (g.point 0) :=
        ((g.mem_ordinaryShared 0).mp (by rw [dg.ordinary_eq]; simp)).2.2
      have eq : g.point 0=f.point 2 := by simpa only [hw,h11,h12] using fg.1
      exact False.elim (ftip2no (eq ▸ go))
    · exact hw
  have gtwo : g.point 2=f.center := by simpa only [wtwo] using gp
  have gone : g.point 1=k.center := by
    have eq : g.point 1=f.point 2 := by simpa only [wtwo,h21,h12] using fg.1
    exact eq.trans kc.symm
  have fk := retained_matching_general G disjoint (by decide : 2≤3) f k df.toChartData
    kinj knc kpos kactual 2 x f2 kx kc kp
  have kprev : k.point (x-1)=f.point 3 := by simpa only [h23] using fk.1
  have knext : k.point (x+1)=g.center := by simpa only [gc,h21] using fk.2
  have kxn : x+1∈k.coreShared := mem_sdiff.mpr ⟨by simp [Sectors.shared,kfull],by
    intro h
    have ord := ((k.mem_ordinaryShared (x+1)).mp h).2.2
    exact gcenterNo (knext ▸ ord)⟩
  have gk := retained_matching_general G disjoint (by decide : 2≤3) g k dg.toChartData
    kinj knc kpos kactual 1 (x+1) g1 kxn gone.symm knext
  have klast : k.point (x+2)=g.point 0 := by
    have eq : (x+1)+1=x+2 := by ring
    simpa only [eq,h11] using gk.2
  let h := UpperOpenMathRotation.Sectors.shift k (x-1)
  have hzero : h.point 0=f.point 3 := by simpa only [h,UpperOpenMathRotation.Sectors.shift_point,add_zero] using kprev
  have hthree : h.point 3=g.point 0 := by
    have eq : x-1+(3 : ZMod (2*3))=x+2 := by ring
    simpa only [h,UpperOpenMathRotation.Sectors.shift_point,eq] using klast
  exact UpperOpenMathTwoCapCycle.three_two_cap_fans_incompatible hL f g h
    (by rw [df.ordinary_eq]; simp) (by rw [dg.ordinary_eq]; simp)
    gc gtwo (by simpa only [h,UpperOpenMathRotation.Sectors.shift_center] using gone)
    (by simpa only [h,UpperOpenMathRotation.Sectors.shift_center] using kc)
    hzero hthree (df.noncentral 1)
    (fun z => knc (x-1+z))

#print axioms retained_matching_general
#print axioms normalized_pair_full_third_impossible
end Kobon.UpperOpenMathNormalizedPairFull
