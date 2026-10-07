import Kobon.UpperOpenMathAntipodalCenterUniqueness

/-! Actual antipodal full triple centers have distinct four-neighbor sets. -/
namespace Kobon.UpperOpenMathAntipodalSameNeighbors
open Cells FanGeometry UpperFan UpperVertexBudget UpperTriangleIncidence
  UpperSharedIncidence UpperCoreExtraction UpperOpenMathAntipodalTwoCapChart
  UpperOpenMathAntipodalCenterUniqueness UpperOpenMathCapHeavyTriples Finset
set_option maxHeartbeats 1000000

theorem charts_outer_center_unique {α : Type*} [Fintype α]
    {n : ℕ} {L : ℕ → Line ℝ} (G : α → TriangleGeometry)
    (f g : Sectors n 3 L) (df : AntipodalData G f) (dg : AntipodalData G g)
    (same : f.coreShared.image f.point=g.coreShared.image g.point) : g.center=f.center := by
  classical
  have outer : f.coreShared.image f.point={f.point 1,f.point 2,f.point 4,f.point 5} := by
    rw [df.core_eq]
    simp
  have mem (w : ZMod 6) (hw : w∈g.coreShared) :
      g.point w∈({f.point 1,f.point 2,f.point 4,f.point 5} : Finset Point) := by
    rw [←outer,same]
    exact mem_image.mpr ⟨w,hw,rfl⟩
  have gm (w : ZMod 6) (hw : w∈g.coreShared) :
      g.point w=f.point 1∨g.point w=f.point 2∨g.point w=f.point 4∨g.point w=f.point 5 := by
    simpa only [mem_insert,mem_singleton] using mem w hw
  apply four_point_center_unique f.center g.center (f.point 1) (f.point 2)
    (f.point 4) (f.point 5) (g.point 1) (g.point 2) (g.point 4) (g.point 5)
  · exact df.positive 1
  · simpa using antipodal_outer_between f 1
  · simpa using antipodal_outer_between f 2
  · simpa using antipodal_outer_between g 1
  · simpa using antipodal_outer_between g 2
  · exact gm 1 (by rw [dg.core_eq]; simp)
  · exact gm 2 (by rw [dg.core_eq]; simp)
  · exact gm 4 (by rw [dg.core_eq]; simp)
  · exact gm 5 (by rw [dg.core_eq]; simp)
  · intro he; exact (by decide : (1 : ZMod 6)≠2) (dg.injective he)
  · intro he; exact (by decide : (1 : ZMod 6)≠4) (dg.injective he)
  · intro he; exact (by decide : (1 : ZMod 6)≠5) (dg.injective he)
  · intro he; exact (by decide : (2 : ZMod 6)≠4) (dg.injective he)
  · intro he; exact (by decide : (2 : ZMod 6)≠5) (dg.injective he)
  · intro he; exact (by decide : (4 : ZMod 6)≠5) (dg.injective he)

noncomputable def coreNeighbors {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (G : α → TriangleGeometry) (c : Point) : Finset Point := by
  classical
  exact (core n L).filter fun q=>{c,q}∈twoCoreEdges n L G

theorem chart_outer_eq_neighbors {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (G : α → TriangleGeometry)
    (f : Sectors n 3 L) (df : AntipodalData G f) :
    f.coreShared.image f.point=coreNeighbors n L G f.center := by
  classical
  ext q
  constructor
  · intro h
    obtain ⟨z,hz,rfl⟩ := mem_image.mp h
    have edge : ({f.center,f.point z} : Edge)∈twoCoreEdges n L G := by
      have h : ({f.center,f.point z} : Edge)∈f.coreShared.image
          (fun z=>({f.center,f.point z} : Edge)) := mem_image.mpr ⟨z,hz,rfl⟩
      rw [df.core_image] at h
      exact (mem_filter.mp h).1
    exact mem_filter.mpr ⟨df.core_endpoint z hz,edge⟩
  · intro h
    have he := (mem_filter.mp h).2
    have hf : ({f.center,q} : Edge)∈f.coreShared.image
        (fun z=>({f.center,f.point z} : Edge)) := by
      rw [df.core_image]
      exact mem_filter.mpr ⟨he,by simp⟩
    obtain ⟨z,hz,pair⟩ := mem_image.mp hf
    have fp : f.point z∈({f.center,q} : Edge) := by rw [←pair]; simp
    have equal : f.point z=q := by
      simpa only [mem_insert,mem_singleton,or_iff_right (df.noncentral z)] using fp
    exact mem_image.mpr ⟨z,hz,equal⟩

/-- Only the two proposed centers need to be triples; other cores may be larger. -/
theorem certificate_anti_same_neighbors_unique {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (c d : Point) (hc : c∈core n L) (hd : d∈core n L)
    (rc : (supports n L c).card=3) (rd : (supports n L d).card=3)
    (ac : ordinaryDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) c=2)
    (ad : ordinaryDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) d=2)
    (dc : coreDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) c=4)
    (dd : coreDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) d=4)
    (mc : UpperOpenMathMarkedPorts.markedCount n L hL hn tri ht c=0)
    (md : UpperOpenMathMarkedPorts.markedCount n L hL hn tri ht d=0)
    (same : coreNeighbors n L (fun a => ofPredicate n L (tri a) hL (ht a)) c=
      coreNeighbors n L (fun a => ofPredicate n L (tri a) hL (ht a)) d) : c=d := by
  let G := fun a => ofPredicate n L (tri a) hL (ht a)
  obtain ⟨f,fc,df⟩ := certificate_antipodal_chart n L hL hn tri hi ht c hc rc ac dc mc
  obtain ⟨g,gd,dg⟩ := certificate_antipodal_chart n L hL hn tri hi ht d hd rd ad dd md
  have fe := chart_outer_eq_neighbors n L G f df
  have ge := chart_outer_eq_neighbors n L G g dg
  rw [fc] at fe
  rw [gd] at ge
  have outerSame : f.coreShared.image f.point=g.coreShared.image g.point := fe.trans (same.trans ge.symm)
  have equal := charts_outer_center_unique G f g df dg outerSame
  rw [fc,gd] at equal
  exact equal.symm

#print axioms charts_outer_center_unique
#print axioms certificate_anti_same_neighbors_unique
end Kobon.UpperOpenMathAntipodalSameNeighbors
