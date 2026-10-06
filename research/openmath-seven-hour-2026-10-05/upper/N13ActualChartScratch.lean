import Kobon.UpperOpenMathAnyChartMatching
import Kobon.UpperOpenMathOneCapThreeCore
import Kobon.UpperOpenMathN13Cases
import Kobon.UpperOpenMathFullCoreSides

namespace Kobon.UpperOpenMathN13ActualChartScratch
open Cells FanGeometry UpperFan UpperVertexBudget UpperTriangleIncidence
  UpperSharedIncidence UpperCoreExtraction UpperOpenMathRadialOrder
  UpperOpenMathSectorRecords UpperOpenMathActualFans UpperOpenMathCapHeavyTriples
  UpperOpenMathAntipodalAdjacency UpperOpenMathAntipodalFullNeighborPair
  UpperOpenMathAntipodalTwoCapChart Finset
set_option maxHeartbeats 1000000

theorem lift_chart_counts {α : Type*} [Fintype α] (G : α → TriangleGeometry)
    {n r : ℕ} [NeZero (2*r)] {L : ℕ → Line ℝ} (f : Sectors n r L) (hr : r=3)
    (inj : Function.Injective f.point) (nc : ∀ z, f.point z≠f.center)
    (pos : ∀ z, 0<areaDet f.center (f.point z) (f.point (z+1)))
    (im : f.coreShared.image (fun z => ({f.center,f.point z} : Edge))=
      (twoCoreEdges n L G).filter (fun e => f.center∈e))
    (occ : ∀ z∈f.triangular, Nonempty (Occurrence G f.center f.point z))
    (ac : f.ordinaryShared.card=1) (dc : f.coreShared.card=3) :
    ∃ g : Sectors n 3 L, g.center=f.center ∧ AnyChartData G g ∧
      g.ordinaryShared.card=1 ∧ g.coreShared.card=3 := by
  subst r
  exact ⟨f,rfl,⟨inj,nc,pos,im,occ⟩,ac,dc⟩

theorem certificate_n13_chart {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (c : Point) (hc : c∈core n L) (rc : (supports n L c).card=3)
    (ac : ordinaryDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) c=1)
    (dc : coreDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) c=3) :
    let G := fun a => ofPredicate n L (tri a) hL (ht a)
    ∃ f : Sectors n 3 L, f.center=c ∧ AnyChartData G f ∧
      f.ordinaryShared.card=1 ∧ f.coreShared.card=3 := by
  classical
  let G := fun a => ofPredicate n L (tri a) hL (ht a)
  letI : NeZero (2*(supports n L c).card) := ⟨by omega⟩
  let D := atPoint n L hL hn c
  let f := fan n L hL hn tri ht c (mem_filter.mp hc).1 D (by omega)
  have occ : ∀ z∈f.triangular, Nonempty (Occurrence G f.center f.point z) := by
    intro z hz
    exact (mem_triangular G c f.point z).mp hz
  exact lift_chart_counts G f rc
    (fan_point_injective n L hL hn tri ht c (mem_filter.mp hc).1 D (by omega))
    (fan_point_ne_center n L hL hn tri ht c (mem_filter.mp hc).1 D (by omega))
    (fan_positive n L hL hn tri ht c (mem_filter.mp hc).1 D (by omega))
    (fan_core_image n L hL hn tri ht c (mem_filter.mp hc).1 D (by omega) hi hc)
    occ
    ((fan_ordinary_card n L hL hn tri ht c (mem_filter.mp hc).1 D (by omega) hi hc).trans ac)
    ((fan_core_card n L hL hn tri ht c (mem_filter.mp hc).1 D (by omega) hi hc).trans dc)

theorem shift_chart_data {α : Type*} [Fintype α] (G : α → TriangleGeometry)
    {n : ℕ} {L : ℕ → Line ℝ} (f : Sectors n 3 L) (df : AnyChartData G f)
    (a : ZMod 6) : AnyChartData G (UpperOpenMathRotation.Sectors.shift f a) := by
  classical
  let g := UpperOpenMathRotation.Sectors.shift f a
  refine ⟨?_,?_,UpperOpenMathRotation.Sectors.shift_positive f df.positive a,?_,?_⟩
  · intro x y h
    exact add_left_cancel (df.injective h)
  · intro z
    exact df.noncentral (a+z)
  · change g.coreShared.image (fun z=>({g.center,g.point z} : Edge))=
      (twoCoreEdges n L G).filter (fun e=>f.center∈e)
    rw [←df.core_image]
    ext e
    constructor
    · intro he
      obtain ⟨z,hz,hze⟩ := mem_image.mp he
      exact mem_image.mpr ⟨a+z,(UpperOpenMathRotation.Sectors.shift_mem_coreShared f a z).mp hz,hze⟩
    · intro he
      obtain ⟨z,hz,hze⟩ := mem_image.mp he
      have cancel : a+(z-a)=z := by ring
      refine mem_image.mpr ⟨z-a,?_,?_⟩
      · apply (UpperOpenMathRotation.Sectors.shift_mem_coreShared f a (z-a)).mpr
        simpa only [cancel] using hz
      · simpa only [g,UpperOpenMathRotation.Sectors.shift_center,
          UpperOpenMathRotation.Sectors.shift_point,cancel] using hze
  · intro z hz
    obtain ⟨o⟩ := df.occurrences (a+z)
      ((UpperOpenMathRotation.Sectors.shift_mem_triangular f a z).mp hz)
    exact ⟨{
      index := o.index, triangle := o.triangle, transport := o.transport
      center := o.center, left := o.left
      right := by simpa only [UpperOpenMathRotation.Sectors.shift_point,add_assoc] using o.right
    }⟩

theorem finite_shift_run : ∀ a z : ZMod 6,
    a+z∈({a-1,a,a+1,a+2,a+3} : Finset (ZMod 6)) ↔
      z∈({5,0,1,2,3} : Finset (ZMod 6)) := by decide +kernel

theorem finite_normalized_shared :
    (({5,0,1,2,3} : Finset (ZMod 6)).filter (fun z=>z-1∈({5,0,1,2,3} : Finset (ZMod 6))))=
      ({0,1,2,3} : Finset (ZMod 6)) := by decide +kernel

theorem normalize_n13_chart {α : Type*} [Fintype α] (G : α → TriangleGeometry)
    {n : ℕ} {L : ℕ → Line ℝ} (f : Sectors n 3 L) (df : AnyChartData G f)
    (ac : f.ordinaryShared.card=1) (dc : f.coreShared.card=3) :
    ∃ g : Sectors n 3 L, g.center=f.center ∧ AnyChartData G g ∧
      g.ordinaryShared.card=1 ∧ g.coreShared.card=3 ∧
      g.triangular=({5,0,1,2,3} : Finset (ZMod 6)) ∧
      g.shared=({0,1,2,3} : Finset (ZMod 6)) := by
  classical
  have sc : f.shared.card=4 := by have hh:=f.shared_card_split; omega
  obtain ⟨a,run,_⟩ := UpperOpenMathN13Cases.four_shared_run f.triangular sc
  let g := UpperOpenMathRotation.Sectors.shift f a
  have gt : g.triangular=({5,0,1,2,3} : Finset (ZMod 6)) := by
    ext z
    rw [UpperOpenMathRotation.Sectors.shift_mem_triangular,run]
    exact finite_shift_run a z
  refine ⟨g,rfl,shift_chart_data G f df a,?_,?_,gt,?_⟩
  · simpa only [g,UpperOpenMathRotation.Sectors.shift_ordinaryShared_card] using ac
  · simpa only [g,UpperOpenMathRotation.Sectors.shift_coreShared_card] using dc
  · change (g.triangular.filter (fun z=>z-1∈g.triangular))=_
    rw [gt]
    exact finite_normalized_shared

#print axioms certificate_n13_chart
#print axioms shift_chart_data
#print axioms normalize_n13_chart

theorem certificate_anti_neighbor_chart {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (triples : ∀ p∈core n L, (supports n L p).card=3)
    (f : Sectors n 3 L)
    (df : AnyChartData (fun a=>ofPredicate n L (tri a) hL (ht a)) f)
    (z : ZMod 6) (hz : z∈f.coreShared)
    (qa : f.point z∈unmarkedFullTwoCapSet n L hL hn tri ht) :
    let G := fun a=>ofPredicate n L (tri a) hL (ht a)
    ∃ g : Sectors n 3 L, ∃ w : ZMod 6, AntipodalData G g ∧
      g.center=f.point z ∧ w∈g.coreShared ∧ g.point w=f.center ∧
      g.point (w-1)=f.point (z+1) ∧ g.point (w+1)=f.point (z-1) := by
  classical
  obtain ⟨qC,qac,qdc,qmc⟩ := mem_filter.mp qa
  obtain ⟨g,gc,dg⟩ := UpperOpenMathAntipodalTwoCapChart.certificate_antipodal_chart
    n L hL hn tri hi ht (f.point z) qC (triples _ qC) qac qdc qmc
  have dgAny : AnyChartData (fun a=>ofPredicate n L (tri a) hL (ht a)) g :=
    ⟨dg.injective,dg.noncentral,dg.positive,dg.core_image,dg.occurrences⟩
  obtain ⟨w,hw,gp,gr,gl⟩ := UpperOpenMathAnyChartMatching.any_charts_neighbor_matching
    n L hL tri hi ht f g df dgAny z hz gc
  exact ⟨g,w,dg,gc,hw,gp,gr,gl⟩

#print axioms certificate_anti_neighbor_chart

theorem certificate_chart_core_endpoint {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L)
    (tri : α → Triple) (ht : ∀ a, TrianglePredicate n L (tri a))
    (f : Sectors n 3 L)
    (df : AnyChartData (fun a=>ofPredicate n L (tri a) hL (ht a)) f)
    (z : ZMod 6) (hz : z∈f.coreShared) : f.point z∈core n L := by
  classical
  let G := fun a=>ofPredicate n L (tri a) hL (ht a)
  have he : ({f.center,f.point z} : Edge)∈twoCoreEdges n L G := by
    have hm : ({f.center,f.point z} : Edge)∈f.coreShared.image
        (fun z=>({f.center,f.point z} : Edge)) := mem_image.mpr ⟨z,hz,rfl⟩
    rw [df.core_image] at hm
    exact (mem_filter.mp hm).1
  have used := (mem_filter.mp (mem_sdiff.mp he).1).1
  exact mem_filter.mpr ⟨UpperEdgeInventory.certificate_side_vertices n L hL tri ht used (by simp),
    twoCore_endpoints n L G he _ (by simp)⟩

theorem certificate_chart_anti_nonadjacent {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (triples : ∀ p∈core n L, (supports n L p).card=3)
    (f : Sectors n 3 L)
    (df : AnyChartData (fun a=>ofPredicate n L (tri a) hL (ht a)) f)
    (z : ZMod 6) (hz : z∈f.coreShared)
    (qa : f.point z∈unmarkedFullTwoCapSet n L hL hn tri ht)
    (ra : f.point (z+1)∈unmarkedFullTwoCapSet n L hL hn tri ht) : False := by
  classical
  let G := fun a=>ofPredicate n L (tri a) hL (ht a)
  have zT : z∈f.triangular := (mem_filter.mp (mem_sdiff.mp hz).1).1
  obtain ⟨o⟩ := df.occurrences z zT
  have cap := transported_side_used G o.index o.triangle o.transport 1
  change ({o.triangle.q,o.triangle.r} : Edge)∈usedEdges G at cap
  rw [o.left,o.right] at cap
  obtain ⟨qC,qa2,qd4,qm0⟩ := mem_filter.mp qa
  obtain ⟨rC,ra2,rd4,rm0⟩ := mem_filter.mp ra
  change ordinaryDegree n L G (f.point z)=2 at qa2
  change coreDegree n L G (f.point z)=4 at qd4
  have rq := triples (f.point z) qC
  have qfull : ordinaryDegree n L G (f.point z)+coreDegree n L G (f.point z)=
      2*(supports n L (f.point z)).card := by omega
  have shared := UpperOpenMathFullCoreSides.certificate_full_core_side_shared
    n L hL hn tri hi ht (f.point z) (f.point (z+1)) qC rC cap qfull
  exact certificate_unmarked_full_not_adjacent n L hL hn tri hi ht triples
    (f.point z) (f.point (z+1)) qC rC qa2 ra2 qd4 rd4 qm0 rm0 shared

#print axioms certificate_chart_core_endpoint
#print axioms certificate_chart_anti_nonadjacent
end Kobon.UpperOpenMathN13ActualChartScratch
