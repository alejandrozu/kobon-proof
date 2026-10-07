import Kobon.UpperOpenMathTripleCharts


/-! The degree-two equality case cannot contain an actual multiple point. -/
namespace Kobon.UpperOpenMathTwoTwoCore
open Cells FanGeometry UpperFan UpperVertexBudget UpperTriangleIncidence
  UpperSharedIncidence UpperCoreExtraction UpperOpenMathRadialOrder
  UpperOpenMathActualFans UpperOpenMathCapHeavyTriples UpperOpenMathTripleCharts Finset

theorem core_edge_of_label {α : Type*} [Fintype α] (G : α → TriangleGeometry)
    {n : ℕ} {L : ℕ → Line ℝ} (f : UpperFan.Sectors n 3 L) (data : ChartData G f)
    (z : ZMod (2*3)) (hz : z∈f.coreShared) :
    {f.center,f.point z}∈twoCoreEdges n L G := by
  classical
  have hm : ({f.center,f.point z} : Edge)∈f.coreShared.image
      (fun z => ({f.center,f.point z} : Edge)) := mem_image.mpr ⟨z,hz,rfl⟩
  rw [data.core_image] at hm
  exact (mem_filter.mp hm).1

theorem reverse_core_label {α : Type*} [Fintype α] (G : α → TriangleGeometry)
    {n : ℕ} {L : ℕ → Line ℝ} (f : UpperFan.Sectors n 3 L) (data : ChartData G f)
    (c : Point) (hne : c≠f.center) (edge : {f.center,c}∈twoCoreEdges n L G) :
    ∃ z : ZMod (2*3), z∈f.coreShared ∧ f.point z=c := by
  classical
  have hm : ({f.center,c} : Edge)∈(twoCoreEdges n L G).filter (fun e => f.center∈e) :=
    mem_filter.mpr ⟨edge,by simp⟩
  rw [← data.core_image] at hm
  obtain ⟨z,hz,he⟩ := mem_image.mp hm
  have hc : c∈({f.center,f.point z} : Edge) := by rw [he]; simp
  rcases mem_insert.mp hc with hc|hc
  · exact False.elim (hne hc)
  · exact ⟨z,hz,(mem_singleton.mp hc).symm⟩

theorem retained_neighbor_matching {α : Type*} [Fintype α] (G : α → TriangleGeometry)
    (disjoint : Pairwise (fun a b => Disjoint (G a).interior (G b).interior))
    {n : ℕ} {L : ℕ → Line ℝ} (f g : UpperFan.Sectors n 3 L)
    (df : ChartData G f) (dg : ChartData G g)
    (z w : ZMod (2*3)) (fz : z∈f.coreShared) (gw : w∈g.coreShared)
    (centerg : g.center=f.point z) (pointg : g.point w=f.center) :
    g.point (w-1)=f.point (z+1) ∧ g.point (w+1)=f.point (z-1) := by
  have fs := (mem_sdiff.mp fz).1
  have gs := (mem_sdiff.mp gw).1
  obtain ⟨fo⟩ := df.occurrences (z-1) (mem_filter.mp fs).2
  obtain ⟨fp⟩ := df.occurrences z (mem_filter.mp fs).1
  obtain ⟨go⟩ := dg.occurrences (w-1) (mem_filter.mp gs).2
  obtain ⟨gp⟩ := dg.occurrences w (mem_filter.mp gs).1
  exact UpperOpenMathFiberMatching.neighboring_points_match G disjoint
    (by decide : 2≤3) (by decide : 2≤3) f.center g.center f.point g.point
    df.injective dg.injective df.noncentral dg.noncentral df.positive dg.positive
    z w centerg pointg fo fp go gp

theorem closed_charts_impossible {α : Type*} [Fintype α]
    {n : ℕ} {L : ℕ → Line ℝ} (hL : NoParallel n L)
    (G : α → TriangleGeometry)
    (disjoint : Pairwise (fun a b => Disjoint (G a).interior (G b).interior))
    (P : Finset Point) (nonempty : P.Nonempty)
    (charts : ∀ c∈P, ∃ f : UpperFan.Sectors n 3 L, f.center=c ∧
      NormalizedData G f ∧ ∀ z∈f.coreShared, f.point z∈P) : False := by
  classical
  obtain ⟨c,hc⟩ := nonempty
  obtain ⟨f,fc,df,fP⟩ := charts c hc
  have f1 : (1 : ZMod (2*3))∈f.coreShared := by rw [df.core_eq]; simp
  have f2 : (2 : ZMod (2*3))∈f.coreShared := by rw [df.core_eq]; simp
  have hu := df.core_endpoint 1 f1
  have hv := df.core_endpoint 2 f2
  obtain ⟨g,gc,dg,gP⟩ := charts (f.point 1) (fP 1 f1)
  have edgefg := core_edge_of_label G f df.toChartData 1 f1
  have edgegf : {g.center,f.center}∈twoCoreEdges n L G := by
    simpa only [gc,pair_comm] using edgefg
  obtain ⟨w,gw,gp⟩ := reverse_core_label G g dg.toChartData f.center
    (by rw [gc]; exact (df.noncentral 1).symm) edgegf
  have fg := retained_neighbor_matching G disjoint f g df.toChartData dg.toChartData 1 w f1 gw gc gp
  have wcase : w=1 ∨ w=2 := by simpa only [dg.core_eq,mem_insert,mem_singleton] using gw
  have wtwo : w=2 := by
    rcases wcase with hw|hw
    · have g0 : OrdinaryAt n L (g.point 0) :=
        ((g.mem_ordinaryShared 0).mp (by rw [dg.ordinary_eq]; simp)).2.2
      have eqv : g.point 0=f.point 2 := by
        have he : (1 : ZMod (2*3))-1=0 := by decide
        have he2 : (1 : ZMod (2*3))+1=2 := by decide
        simpa only [hw,he,he2] using fg.1
      exact False.elim ((mem_filter.mp hv).2 (eqv ▸ g0))
    · exact hw
  have gtwo : g.point 2=f.center := by simpa only [wtwo] using gp
  have gone : g.point 1=f.point 2 := by
    have he : (2 : ZMod (2*3))-1=1 := by decide
    have he2 : (1 : ZMod (2*3))+1=2 := by decide
    simpa only [wtwo,he,he2] using fg.1
  obtain ⟨k,kc,dk,kP⟩ := charts (f.point 2) (fP 2 f2)
  have edgefk := core_edge_of_label G f df.toChartData 2 f2
  have edgekf : {k.center,f.center}∈twoCoreEdges n L G := by
    simpa only [kc,pair_comm] using edgefk
  obtain ⟨x,kx,kp⟩ := reverse_core_label G k dk.toChartData f.center
    (by rw [kc]; exact (df.noncentral 2).symm) edgekf
  have fk := retained_neighbor_matching G disjoint f k df.toChartData dk.toChartData 2 x f2 kx kc kp
  have xcase : x=1 ∨ x=2 := by simpa only [dk.core_eq,mem_insert,mem_singleton] using kx
  have xone : x=1 := by
    rcases xcase with hx|hx
    · exact hx
    · have k3 : OrdinaryAt n L (k.point 3) :=
        ((k.mem_ordinaryShared 3).mp (by rw [dk.ordinary_eq]; simp)).2.2
      have equ : k.point 3=f.point 1 := by
        have he : (2 : ZMod (2*3))+1=3 := by decide
        have he2 : (2 : ZMod (2*3))-1=1 := by decide
        simpa only [hx,he,he2] using fk.2
      exact False.elim ((mem_filter.mp hu).2 (equ ▸ k3))
  have kzero : k.point 0=f.point 3 := by
    have he : (1 : ZMod (2*3))-1=0 := by decide
    have he2 : (2 : ZMod (2*3))+1=3 := by decide
    simpa only [xone,he,he2] using fk.1
  have ktwo : k.point 2=g.center := by
    have he : (1 : ZMod (2*3))+1=2 := by decide
    have he2 : (2 : ZMod (2*3))-1=1 := by decide
    simpa only [xone,he,he2,gc] using fk.2
  have g1 : (1 : ZMod (2*3))∈g.coreShared := by rw [dg.core_eq]; simp
  have k2 : (2 : ZMod (2*3))∈k.coreShared := by rw [dk.core_eq]; simp
  have gk := retained_neighbor_matching G disjoint g k dg.toChartData dk.toChartData 1 2 g1 k2
    (kc.trans gone.symm) ktwo
  have kthree : k.point 3=g.point 0 := by
    have he : (2 : ZMod (2*3))+1=3 := by decide
    have he2 : (1 : ZMod (2*3))-1=0 := by decide
    simpa only [he,he2] using gk.2
  exact UpperOpenMathTwoCapCycle.three_two_cap_fans_incompatible hL f g k
    (by rw [df.ordinary_eq]; simp) (by rw [dg.ordinary_eq]; simp)
    gc gtwo (gone.trans kc.symm) kc kzero kthree (df.noncentral 1) dk.noncentral



theorem certificate_two_two_core_empty {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (triples : ∀ c∈core n L, (supports n L c).card=3)
    (ordinary_two : ∀ c∈core n L, ordinaryDegree n L
      (fun a => ofPredicate n L (tri a) hL (ht a)) c=2)
    (core_two : ∀ c∈core n L, coreDegree n L
      (fun a => ofPredicate n L (tri a) hL (ht a)) c=2) : core n L=∅ := by
  classical
  by_contra hne
  obtain ⟨c,hc⟩ := nonempty_iff_ne_empty.mpr hne
  let G := fun a => ofPredicate n L (tri a) hL (ht a)
  have disjoint : Pairwise (fun a b => Disjoint (G a).interior (G b).interior) := by
    intro a b hab
    exact distinct_interiors_disjoint n L _ _ hL (ht a) (ht b) (fun he => hab (hi he))
  obtain ⟨f,fc,df⟩ := certificate_normalized_chart n L hL hn tri hi ht triples ordinary_two core_two c hc
  have f1 : (1 : ZMod (2*3))∈f.coreShared := by rw [df.core_eq]; simp
  have f2 : (2 : ZMod (2*3))∈f.coreShared := by rw [df.core_eq]; simp
  have hu := df.core_endpoint 1 f1
  have hv := df.core_endpoint 2 f2
  obtain ⟨g,gc,dg⟩ := certificate_normalized_chart n L hL hn tri hi ht triples ordinary_two core_two (f.point 1) hu
  have edgefg := core_edge_of_label G f df.toChartData 1 f1
  have edgegf : {g.center,f.center}∈twoCoreEdges n L G := by
    simpa only [gc,pair_comm] using edgefg
  obtain ⟨w,gw,gp⟩ := reverse_core_label G g dg.toChartData f.center
    (by rw [gc]; exact (df.noncentral 1).symm) edgegf
  have fg := retained_neighbor_matching G disjoint f g df.toChartData dg.toChartData 1 w f1 gw gc gp
  have wcase : w=1 ∨ w=2 := by simpa only [dg.core_eq,mem_insert,mem_singleton] using gw
  have wtwo : w=2 := by
    rcases wcase with hw|hw
    · have g0 : OrdinaryAt n L (g.point 0) :=
        ((g.mem_ordinaryShared 0).mp (by rw [dg.ordinary_eq]; simp)).2.2
      have eqv : g.point 0=f.point 2 := by
        have he : (1 : ZMod (2*3))-1=0 := by decide
        have he2 : (1 : ZMod (2*3))+1=2 := by decide
        simpa only [hw,he,he2] using fg.1
      exact False.elim ((mem_filter.mp hv).2 (eqv ▸ g0))
    · exact hw
  have gtwo : g.point 2=f.center := by simpa only [wtwo] using gp
  have gone : g.point 1=f.point 2 := by
    have he : (2 : ZMod (2*3))-1=1 := by decide
    have he2 : (1 : ZMod (2*3))+1=2 := by decide
    simpa only [wtwo,he,he2] using fg.1
  obtain ⟨k,kc,dk⟩ := certificate_normalized_chart n L hL hn tri hi ht triples ordinary_two core_two (f.point 2) hv
  have edgefk := core_edge_of_label G f df.toChartData 2 f2
  have edgekf : {k.center,f.center}∈twoCoreEdges n L G := by
    simpa only [kc,pair_comm] using edgefk
  obtain ⟨x,kx,kp⟩ := reverse_core_label G k dk.toChartData f.center
    (by rw [kc]; exact (df.noncentral 2).symm) edgekf
  have fk := retained_neighbor_matching G disjoint f k df.toChartData dk.toChartData 2 x f2 kx kc kp
  have xcase : x=1 ∨ x=2 := by simpa only [dk.core_eq,mem_insert,mem_singleton] using kx
  have xone : x=1 := by
    rcases xcase with hx|hx
    · exact hx
    · have k3 : OrdinaryAt n L (k.point 3) :=
        ((k.mem_ordinaryShared 3).mp (by rw [dk.ordinary_eq]; simp)).2.2
      have equ : k.point 3=f.point 1 := by
        have he : (2 : ZMod (2*3))+1=3 := by decide
        have he2 : (2 : ZMod (2*3))-1=1 := by decide
        simpa only [hx,he,he2] using fk.2
      exact False.elim ((mem_filter.mp hu).2 (equ ▸ k3))
  have kzero : k.point 0=f.point 3 := by
    have he : (1 : ZMod (2*3))-1=0 := by decide
    have he2 : (2 : ZMod (2*3))+1=3 := by decide
    simpa only [xone,he,he2] using fk.1
  have ktwo : k.point 2=g.center := by
    have he : (1 : ZMod (2*3))+1=2 := by decide
    have he2 : (2 : ZMod (2*3))-1=1 := by decide
    simpa only [xone,he,he2,gc] using fk.2
  have g1 : (1 : ZMod (2*3))∈g.coreShared := by rw [dg.core_eq]; simp
  have k2 : (2 : ZMod (2*3))∈k.coreShared := by rw [dk.core_eq]; simp
  have gk := retained_neighbor_matching G disjoint g k dg.toChartData dk.toChartData 1 2 g1 k2
    (kc.trans gone.symm) ktwo
  have kthree : k.point 3=g.point 0 := by
    have he : (2 : ZMod (2*3))+1=3 := by decide
    have he2 : (1 : ZMod (2*3))-1=0 := by decide
    simpa only [he,he2] using gk.2
  exact UpperOpenMathTwoCapCycle.three_two_cap_fans_incompatible hL f g k
    (by rw [df.ordinary_eq]; simp) (by rw [dg.ordinary_eq]; simp)
    gc gtwo (gone.trans kc.symm) kc kzero kthree (df.noncentral 1) dk.noncentral


theorem certificate_closed_two_two_impossible {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (P : Finset Point) (sub : P⊆core n L) (nonempty : P.Nonempty)
    (closed : UpperOpenMathCoreComponents.SharedCoreClosed n L
      (fun a => ofPredicate n L (tri a) hL (ht a)) P)
    (rigid : ∀ c∈P, (supports n L c).card=3 ∧
      ordinaryDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) c=2 ∧
      coreDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) c=2) : False := by
  let G := fun a => ofPredicate n L (tri a) hL (ht a)
  have disjoint : Pairwise (fun a b => Disjoint (G a).interior (G b).interior) := by
    intro a b hab
    exact distinct_interiors_disjoint n L _ _ hL (ht a) (ht b) (fun he => hab (hi he))
  exact closed_charts_impossible hL G disjoint P nonempty
    (certificate_closed_normalized_chart n L hL hn tri hi ht P sub closed rigid)

#print axioms certificate_two_two_core_empty
#print axioms certificate_closed_two_two_impossible
end Kobon.UpperOpenMathTwoTwoCore
