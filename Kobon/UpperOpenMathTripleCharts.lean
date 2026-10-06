import Kobon.UpperOpenMathTwoCapCycle
import Kobon.UpperOpenMathCoreComponents

/-! Canonical normalized charts for the actual degree-two rigidity case. -/
namespace Kobon.UpperOpenMathTripleCharts
open Cells FanGeometry UpperFan UpperVertexBudget UpperTriangleIncidence
  UpperSharedIncidence UpperCoreExtraction UpperOpenMathRadialOrder
  UpperOpenMathActualFans UpperOpenMathCapHeavyTriples Finset

structure ChartData {α : Type*} [Fintype α] (G : α → TriangleGeometry)
    {n : ℕ} {L : ℕ → Line ℝ} (f : UpperFan.Sectors n 3 L) : Prop where
  injective : Function.Injective f.point
  noncentral : ∀ z, f.point z≠f.center
  positive : ∀ z, 0<areaDet f.center (f.point z) (f.point (z+1))
  ordinary_card : f.ordinaryShared.card=2
  core_card : f.coreShared.card=2
  core_endpoint : ∀ z∈f.coreShared, f.point z∈core n L
  core_image : f.coreShared.image (fun z => ({f.center,f.point z} : Edge))=
    (twoCoreEdges n L G).filter (fun e => f.center∈e)
  occurrences : ∀ z∈f.triangular,
    Nonempty (UpperOpenMathSectorRecords.Occurrence G f.center f.point z)
  no_mark : ∀ z∈f.coreShared, ¬(z-1∈f.ordinaryShared ∧ z+1∈f.ordinaryShared)

structure NormalizedData {α : Type*} [Fintype α] (G : α → TriangleGeometry)
    {n : ℕ} {L : ℕ → Line ℝ} (f : UpperFan.Sectors n 3 L) : Prop extends ChartData G f where
  ordinary_eq : f.ordinaryShared={0,3}
  core_eq : f.coreShared={1,2}

theorem lift_three {α : Type*} [Fintype α] (G : α → TriangleGeometry)
    {n r : ℕ} [NeZero (2*r)] {L : ℕ → Line ℝ} (hr : r=3)
    (f : UpperFan.Sectors n r L)
    (inj : Function.Injective f.point) (nc : ∀ z, f.point z≠f.center)
    (pos : ∀ z, 0<areaDet f.center (f.point z) (f.point (z+1)))
    (ord : f.ordinaryShared.card=2) (cor : f.coreShared.card=2)
    (ce : ∀ z∈f.coreShared, f.point z∈core n L)
    (im : f.coreShared.image (fun z => ({f.center,f.point z} : Edge))=
      (twoCoreEdges n L G).filter (fun e => f.center∈e))
    (occ : ∀ z∈f.triangular, Nonempty
      (UpperOpenMathSectorRecords.Occurrence G f.center f.point z))
    (nm : ∀ z∈f.coreShared, ¬(z-1∈f.ordinaryShared ∧ z+1∈f.ordinaryShared)) :
    ∃ g : UpperFan.Sectors n 3 L, g.center=f.center ∧ ChartData G g := by
  subst r
  exact ⟨f,rfl,⟨inj,nc,pos,ord,cor,ce,im,occ,nm⟩⟩

theorem shifted_data {α : Type*} [Fintype α] (G : α → TriangleGeometry)
    {n : ℕ} {L : ℕ → Line ℝ} (f : UpperFan.Sectors n 3 L)
    (data : ChartData G f) (a : ZMod (2*3)) :
    ChartData G (UpperOpenMathRotation.Sectors.shift f a) := by
  classical
  let g := UpperOpenMathRotation.Sectors.shift f a
  refine ⟨?_,?_,UpperOpenMathRotation.Sectors.shift_positive f data.positive a,
    ?_,?_,?_,?_,?_,?_⟩
  · intro x y he
    exact add_left_cancel (data.injective he)
  · intro z
    exact data.noncentral (a+z)
  · simpa only [UpperOpenMathRotation.Sectors.shift_ordinaryShared_card] using data.ordinary_card
  · simpa only [UpperOpenMathRotation.Sectors.shift_coreShared_card] using data.core_card
  · intro z hz
    exact data.core_endpoint (a+z) ((UpperOpenMathRotation.Sectors.shift_mem_coreShared f a z).mp hz)
  · change g.coreShared.image (fun z => ({g.center,g.point z} : Edge))=
      (twoCoreEdges n L G).filter (fun e => f.center∈e)
    rw [← data.core_image]
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
    have hza := (UpperOpenMathRotation.Sectors.shift_mem_triangular f a z).mp hz
    obtain ⟨o⟩ := data.occurrences (a+z) hza
    exact ⟨{
      index := o.index
      triangle := o.triangle
      transport := o.transport
      center := o.center
      left := o.left
      right := by simpa only [UpperOpenMathRotation.Sectors.shift_point,add_assoc] using o.right
    }⟩
  · intro z hz hh
    apply data.no_mark (a+z) ((UpperOpenMathRotation.Sectors.shift_mem_coreShared f a z).mp hz)
    constructor
    · have hp := (UpperOpenMathRotation.Sectors.shift_mem_ordinaryShared f a (z-1)).mp hh.1
      simpa only [add_sub_assoc] using hp
    · have hp := (UpperOpenMathRotation.Sectors.shift_mem_ordinaryShared f a (z+1)).mp hh.2
      simpa only [add_assoc] using hp

theorem normalized_exists {α : Type*} [Fintype α] (G : α → TriangleGeometry)
    {n : ℕ} {L : ℕ → Line ℝ} (f : UpperFan.Sectors n 3 L) (data : ChartData G f) :
    ∃ g : UpperFan.Sectors n 3 L, g.center=f.center ∧ NormalizedData G g := by
  classical
  obtain ⟨a,ha,ha3,ha1,ha2⟩ := UpperOpenMathTwoCapCycle.normalized_two_cap_anchor
    f data.ordinary_card data.core_card data.no_mark
  let g := UpperOpenMathRotation.Sectors.shift f a
  have dg := shifted_data G f data a
  have go0 : (0 : ZMod (2*3))∈g.ordinaryShared := by
    apply (UpperOpenMathRotation.Sectors.shift_mem_ordinaryShared f a 0).mpr
    simpa only [add_zero] using ha
  have go3 : (3 : ZMod (2*3))∈g.ordinaryShared :=
    (UpperOpenMathRotation.Sectors.shift_mem_ordinaryShared f a 3).mpr ha3
  have gc1 : (1 : ZMod (2*3))∈g.coreShared :=
    (UpperOpenMathRotation.Sectors.shift_mem_coreShared f a 1).mpr ha1
  have gc2 : (2 : ZMod (2*3))∈g.coreShared :=
    (UpperOpenMathRotation.Sectors.shift_mem_coreShared f a 2).mpr ha2
  have oge : g.ordinaryShared={0,3} := by
    apply Eq.symm
    apply eq_of_subset_of_card_le
    · intro z hz
      rcases mem_insert.mp hz with hz|hz
      · simpa only [hz] using go0
      · simpa only [mem_singleton.mp hz] using go3
    · rw [dg.ordinary_card]
      decide
  have cge : g.coreShared={1,2} := by
    apply Eq.symm
    apply eq_of_subset_of_card_le
    · intro z hz
      rcases mem_insert.mp hz with hz|hz
      · simpa only [hz] using gc1
      · simpa only [mem_singleton.mp hz] using gc2
    · rw [dg.core_card]
      decide
  exact ⟨g,rfl,⟨dg,oge,cge⟩⟩

theorem certificate_normalized_chart {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (triples : ∀ c∈core n L, (supports n L c).card=3)
    (ordinary_two : ∀ c∈core n L, ordinaryDegree n L
      (fun a => ofPredicate n L (tri a) hL (ht a)) c=2)
    (core_two : ∀ c∈core n L, coreDegree n L
      (fun a => ofPredicate n L (tri a) hL (ht a)) c=2)
    (c : Point) (hc : c∈core n L) :
    ∃ f : UpperFan.Sectors n 3 L, f.center=c ∧
      NormalizedData (fun a => ofPredicate n L (tri a) hL (ht a)) f := by
  classical
  let G := fun a => ofPredicate n L (tri a) hL (ht a)
  have rc := triples c hc
  letI : NeZero (2*(supports n L c).card) := ⟨by omega⟩
  let D := atPoint n L hL hn c
  let f := fan n L hL hn tri ht c (mem_filter.mp hc).1 D (by omega)
  have ord : f.ordinaryShared.card=2 := by
    rw [fan_ordinary_card n L hL hn tri ht c (mem_filter.mp hc).1 D (by omega) hi hc]
    exact ordinary_two c hc
  have cor : f.coreShared.card=2 := by
    rw [fan_core_card n L hL hn tri ht c (mem_filter.mp hc).1 D (by omega) hi hc]
    exact core_two c hc
  have ce : ∀ z∈f.coreShared, f.point z∈core n L :=
    fan_core_endpoint n L hL hn tri ht c (mem_filter.mp hc).1 D (by omega) hi hc
  have im : f.coreShared.image (fun z => ({f.center,f.point z} : Edge))=
      (twoCoreEdges n L G).filter (fun e => f.center∈e) :=
    fan_core_image n L hL hn tri ht c (mem_filter.mp hc).1 D (by omega) hi hc
  have occ : ∀ z∈f.triangular, Nonempty
      (UpperOpenMathSectorRecords.Occurrence G f.center f.point z) := by
    intro z hz
    exact (UpperOpenMathSectorRecords.mem_triangular G c f.point z).mp hz
  have nm : ∀ z∈f.coreShared, ¬(z-1∈f.ordinaryShared ∧ z+1∈f.ordinaryShared) :=
    UpperOpenMathTwoCapCycle.certificate_no_mark n L hL hn tri hi ht triples ordinary_two c hc D (by omega)
  obtain ⟨g,hg,dg⟩ := lift_three G rc f
    (fan_point_injective n L hL hn tri ht c (mem_filter.mp hc).1 D (by omega))
    (fan_point_ne_center n L hL hn tri ht c (mem_filter.mp hc).1 D (by omega))
    (fan_positive n L hL hn tri ht c (mem_filter.mp hc).1 D (by omega))
    ord cor ce im occ nm
  obtain ⟨h,hh,dh⟩ := normalized_exists G g dg
  exact ⟨h,hh.trans hg,dh⟩

theorem certificate_local_normalized_chart {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (c : Point) (hc : c∈core n L) (rc : (supports n L c).card=3)
    (ordc : ordinaryDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) c=2)
    (corc : coreDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) c=2)
    (neighbors : ∀ d∈core n L,
      {c,d}∈twoCoreEdges n L (fun a => ofPredicate n L (tri a) hL (ht a)) →
      (supports n L d).card=3 ∧ ordinaryDegree n L
        (fun a => ofPredicate n L (tri a) hL (ht a)) d=2) :
    ∃ f : UpperFan.Sectors n 3 L, f.center=c ∧
      NormalizedData (fun a => ofPredicate n L (tri a) hL (ht a)) f := by
  classical
  let G := fun a => ofPredicate n L (tri a) hL (ht a)
  letI : NeZero (2*(supports n L c).card) := ⟨by omega⟩
  let D := atPoint n L hL hn c
  let f := fan n L hL hn tri ht c (mem_filter.mp hc).1 D (by omega)
  have ord : f.ordinaryShared.card=2 := by
    rw [fan_ordinary_card n L hL hn tri ht c (mem_filter.mp hc).1 D (by omega) hi hc]
    exact ordc
  have cor : f.coreShared.card=2 := by
    rw [fan_core_card n L hL hn tri ht c (mem_filter.mp hc).1 D (by omega) hi hc]
    exact corc
  have ce : ∀ z∈f.coreShared, f.point z∈core n L :=
    fan_core_endpoint n L hL hn tri ht c (mem_filter.mp hc).1 D (by omega) hi hc
  have im : f.coreShared.image (fun z => ({f.center,f.point z} : Edge))=
      (twoCoreEdges n L G).filter (fun e => f.center∈e) :=
    fan_core_image n L hL hn tri ht c (mem_filter.mp hc).1 D (by omega) hi hc
  have occ : ∀ z∈f.triangular, Nonempty
      (UpperOpenMathSectorRecords.Occurrence G f.center f.point z) := by
    intro z hz
    exact (UpperOpenMathSectorRecords.mem_triangular G c f.point z).mp hz
  have nm : ∀ z∈f.coreShared, ¬(z-1∈f.ordinaryShared ∧ z+1∈f.ordinaryShared) := by
    intro z hz marked
    let d := f.point z
    have hd := ce z hz
    have he := (fan_core_iff n L hL hn tri ht c (mem_filter.mp hc).1 D (by omega) hi hc z).mp hz
    obtain ⟨rd,ordd⟩ := neighbors d hd he
    letI : NeZero (2*(supports n L d).card) := ⟨by omega⟩
    let E := atPoint n L hL hn d
    let g := fan n L hL hn tri ht d (mem_filter.mp hd).1 E (by omega)
    obtain ⟨w,gcore,gw,right,left⟩ := UpperOpenMathActualMatching.certificate_neighbor_matching
      n L hL hn tri hi ht c d hc hd D E (by omega) (by omega) z hz rfl
    have poor := UpperOpenMathMarkedPoverty.marked_neighbor_poverty_sum_card
      rc rd hL f g z w marked.1 marked.2 gcore rfl gw right left
      (fan_positive n L hL hn tri ht c (mem_filter.mp hc).1 D (by omega))
    have hg : g.ordinaryShared.card=2 := by
      rw [fan_ordinary_card n L hL hn tri ht d (mem_filter.mp hd).1 E (by omega) hi hd]
      exact ordd
    omega
  obtain ⟨g,hg,dg⟩ := lift_three G rc f
    (fan_point_injective n L hL hn tri ht c (mem_filter.mp hc).1 D (by omega))
    (fan_point_ne_center n L hL hn tri ht c (mem_filter.mp hc).1 D (by omega))
    (fan_positive n L hL hn tri ht c (mem_filter.mp hc).1 D (by omega))
    ord cor ce im occ nm
  obtain ⟨h,hh,dh⟩ := normalized_exists G g dg
  exact ⟨h,hh.trans hg,dh⟩

theorem certificate_closed_normalized_chart {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (P : Finset Point) (sub : P⊆core n L)
    (closed : UpperOpenMathCoreComponents.SharedCoreClosed n L
      (fun a => ofPredicate n L (tri a) hL (ht a)) P)
    (rigid : ∀ c∈P, (supports n L c).card=3 ∧
      ordinaryDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) c=2 ∧
      coreDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) c=2)
    (c : Point) (hc : c∈P) :
    ∃ f : UpperFan.Sectors n 3 L, f.center=c ∧
      NormalizedData (fun a => ofPredicate n L (tri a) hL (ht a)) f ∧
      ∀ z∈f.coreShared, f.point z∈P := by
  classical
  let G := fun a => ofPredicate n L (tri a) hL (ht a)
  obtain ⟨rc,ordc,corc⟩ := rigid c hc
  have neighbors (d : Point) (hd : d∈core n L) (he : {c,d}∈twoCoreEdges n L G) :
      (supports n L d).card=3 ∧ ordinaryDegree n L G d=2 := by
    have hdP : d∈P := closed {c,d} he c (by simp) hc (by simp)
    exact ⟨(rigid d hdP).1,(rigid d hdP).2.1⟩
  obtain ⟨f,fc,df⟩ := certificate_local_normalized_chart n L hL hn tri hi ht c (sub hc) rc ordc corc neighbors
  refine ⟨f,fc,df,?_⟩
  intro z hz
  have he : ({f.center,f.point z} : Edge)∈f.coreShared.image
      (fun z => ({f.center,f.point z} : Edge)) := mem_image.mpr ⟨z,hz,rfl⟩
  rw [df.core_image] at he
  have hD2 := (mem_filter.mp he).1
  exact closed _ hD2 f.center (by simp) (by simpa only [fc] using hc) (by simp)

#print axioms certificate_normalized_chart
#print axioms certificate_closed_normalized_chart
end Kobon.UpperOpenMathTripleCharts
