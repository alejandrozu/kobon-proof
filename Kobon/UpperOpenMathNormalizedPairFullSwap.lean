import Kobon.UpperOpenMathNormalizedPairFull

/-! The second orientation of the normalized-pair/full-third obstruction. -/
namespace Kobon.UpperOpenMathNormalizedPairFullSwap
open Cells FanGeometry UpperFan UpperOpenMathTripleCharts UpperOpenMathTwoTwoCore Finset
set_option maxHeartbeats 1000000

theorem normalized_swapped_pair_full_third_impossible {α : Type*} [Fintype α]
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
    (gc : g.center=f.point 2) (gp : g.point w=f.center)
    (kc : k.center=f.point 1) (kp : k.point x=f.center) : False := by
  classical
  have h11 : (1 : ZMod (2*3))-1=0 := by decide
  have h12 : (1 : ZMod (2*3))+1=2 := by decide
  have h21 : (2 : ZMod (2*3))-1=1 := by decide
  have h23 : (2 : ZMod (2*3))+1=3 := by decide
  have f1 : (1 : ZMod (2*3))∈f.coreShared := by rw [df.core_eq]; simp
  have f2 : (2 : ZMod (2*3))∈f.coreShared := by rw [df.core_eq]; simp
  have f3o : OrdinaryAt n L (f.point 3) :=
    ((f.mem_ordinaryShared 3).mp (by rw [df.ordinary_eq]; simp)).2.2
  have fg := retained_neighbor_matching G disjoint f g df.toChartData dg.toChartData 2 w f2 gw gc gp
  have wone : w=1 := by
    have cases : w=1 ∨ w=2 := by simpa only [dg.core_eq,mem_insert,mem_singleton] using gw
    rcases cases with hw|hw
    · exact hw
    · have gn : ¬OrdinaryAt n L (g.point 1) :=
        (mem_filter.mp (dg.core_endpoint 1 (by rw [dg.core_eq]; simp))).2
      have eq : g.point 1=f.point 3 := by simpa only [hw,h21,h23] using fg.1
      exact False.elim (gn (eq.symm ▸ f3o))
  have gone : g.point 1=f.center := by simpa only [wone] using gp
  have gtwo : g.point 2=k.center := by
    have eq : g.point 2=f.point 1 := by simpa only [wone,h12,h21] using fg.2
    exact eq.trans kc.symm
  have fk := UpperOpenMathNormalizedPairFull.retained_matching_general G disjoint
    (by decide : 2≤3) f k df.toChartData kinj knc kpos kactual 1 x f1 kx kc kp
  have kprev : k.point (x-1)=g.center := by simpa only [h12,gc] using fk.1
  have gn : ¬OrdinaryAt n L g.center := by
    rw [gc]
    exact (mem_filter.mp (df.core_endpoint 2 f2)).2
  have kxc : x-1∈k.coreShared := mem_sdiff.mpr ⟨by simp [Sectors.shared,kfull],by
    intro ho
    have oo := ((k.mem_ordinaryShared (x-1)).mp ho).2.2
    exact gn (kprev ▸ oo)⟩
  have fincoming : (2 : ZMod (2*3))∈f.coreShared := f2
  exact UpperOpenMathNormalizedPairFull.normalized_pair_full_third_impossible
    G disjoint hL g f k dg df kinj knc kpos kactual kfull 2 (x-1)
    fincoming kxc gone.symm gc.symm gtwo.symm kprev

#print axioms normalized_swapped_pair_full_third_impossible
end Kobon.UpperOpenMathNormalizedPairFullSwap
