import Kobon.UpperOpenMathAntipodalFullNeighborPair

/-! Actual neighboring endpoint extraction from arbitrary triple charts.
Neither source chart is assumed to have a full fan or two ordinary caps. -/
namespace Kobon.UpperOpenMathAnyChartMatching
open Cells FanGeometry UpperFan UpperVertexBudget UpperTriangleIncidence
  UpperSharedIncidence UpperOpenMathSectorRecords
  UpperOpenMathAntipodalFullNeighborPair Finset
set_option maxHeartbeats 1000000

theorem any_charts_neighbor_matching {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (f g : Sectors n 3 L)
    (df : AnyChartData (fun a => ofPredicate n L (tri a) hL (ht a)) f)
    (dg : AnyChartData (fun a => ofPredicate n L (tri a) hL (ht a)) g)
    (z : ZMod 6) (hz : z∈f.coreShared) (center : g.center=f.point z) :
    ∃ w : ZMod 6, w∈g.coreShared ∧ g.point w=f.center ∧
      g.point (w-1)=f.point (z+1) ∧ g.point (w+1)=f.point (z-1) := by
  classical
  let G := fun a => ofPredicate n L (tri a) hL (ht a)
  have pairUsed : ({f.center,f.point z} : Edge)∈twoCoreEdges n L G := by
    have hm : ({f.center,f.point z} : Edge)∈f.coreShared.image
        (fun z=>({f.center,f.point z} : Edge)) := mem_image.mpr ⟨z,hz,rfl⟩
    rw [df.core_image] at hm
    exact (mem_filter.mp hm).1
  have he : {g.center,f.center}∈twoCoreEdges n L G := by
    simpa only [center,pair_comm] using pairUsed
  have hm : ({g.center,f.center} : Edge)∈g.coreShared.image
      (fun w=>({g.center,g.point w} : Edge)) := by
    rw [dg.core_image]
    exact mem_filter.mpr ⟨he,by simp⟩
  obtain ⟨w,hw,hpair⟩ := mem_image.mp hm
  have hc : g.point w=f.center := by
    have hm : f.center∈({g.center,g.point w} : Edge) := by rw [hpair]; simp
    simp only [mem_insert,mem_singleton] at hm
    rcases hm with h|h
    · exact False.elim (df.noncentral z (center.symm.trans h.symm))
    · exact h.symm
  have fshared := (mem_sdiff.mp hz).1
  have gshared := (mem_sdiff.mp hw).1
  obtain ⟨o⟩ := df.occurrences (z-1) (mem_filter.mp fshared).2
  obtain ⟨p⟩ := df.occurrences z (mem_filter.mp fshared).1
  obtain ⟨a⟩ := dg.occurrences (w-1) (mem_filter.mp gshared).2
  obtain ⟨b⟩ := dg.occurrences w (mem_filter.mp gshared).1
  have disjoint : Pairwise (fun a b=>Disjoint (G a).interior (G b).interior) := by
    intro a b hab
    exact distinct_interiors_disjoint n L _ _ hL (ht a) (ht b) (fun h=>hab (hi h))
  have matching := UpperOpenMathFiberMatching.neighboring_points_match G disjoint
    (by decide : 2≤3) (by decide : 2≤3) f.center g.center f.point g.point
    df.injective dg.injective df.noncentral dg.noncentral df.positive dg.positive
    z w center hc o p a b
  exact ⟨w,hw,hc,matching⟩

#print axioms any_charts_neighbor_matching
end Kobon.UpperOpenMathAnyChartMatching
