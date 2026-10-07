import Kobon.UpperOpenMathMarkedPorts
import Kobon.UpperOpenMathMarkedCurvatureWeights
import Kobon.UpperOpenMathFullSharing

/-! Actual normalized charts for unmarked full two-cap triple fans. -/
namespace Kobon.UpperOpenMathAntipodalTwoCapChart
open Cells FanGeometry UpperFan UpperVertexBudget UpperTriangleIncidence UpperSharedIncidence
  UpperCoreExtraction UpperOpenMathCapHeavyTriples UpperOpenMathActualFans
  UpperOpenMathRadialOrder UpperOpenMathMarkedPorts Finset

structure FullData {α : Type*} [Fintype α] (G : α → TriangleGeometry)
    {n : ℕ} {L : ℕ → Line ℝ} (f : UpperFan.Sectors n 3 L) : Prop where
  injective : Function.Injective f.point
  noncentral : ∀ z, f.point z≠f.center
  positive : ∀ z, 0<areaDet f.center (f.point z) (f.point (z+1))
  ordinary_card : f.ordinaryShared.card=2
  core_card : f.coreShared.card=4
  core_endpoint : ∀ z∈f.coreShared, f.point z∈core n L
  core_image : f.coreShared.image (fun z => ({f.center,f.point z} : Edge))=
    (twoCoreEdges n L G).filter (fun e => f.center∈e)
  occurrences : ∀ z∈f.triangular,
    Nonempty (UpperOpenMathSectorRecords.Occurrence G f.center f.point z)
  no_mark : ∀ z∈f.coreShared, ¬(z-1∈f.ordinaryShared ∧ z+1∈f.ordinaryShared)

structure AntipodalData {α : Type*} [Fintype α] (G : α → TriangleGeometry)
    {n : ℕ} {L : ℕ → Line ℝ} (f : UpperFan.Sectors n 3 L) : Prop extends FullData G f where
  ordinary_eq : f.ordinaryShared={0,3}
  core_eq : f.coreShared={1,2,4,5}
  triangular_eq : f.triangular=univ

theorem full_triangular {α : Type*} [Fintype α] (G : α → TriangleGeometry)
    {n : ℕ} {L : ℕ → Line ℝ} (f : UpperFan.Sectors n 3 L) (data : FullData G f) :
    f.triangular=univ := by
  have hc := f.shared_card_split
  rw [data.ordinary_card,data.core_card] at hc
  exact UpperOpenMathFullSharing.shared_full f (by omega)

theorem full_shared {α : Type*} [Fintype α] (G : α → TriangleGeometry)
    {n : ℕ} {L : ℕ → Line ℝ} (f : UpperFan.Sectors n 3 L) (data : FullData G f) :
    f.shared=univ := by
  classical
  ext z
  simp [UpperFan.Sectors.shared,full_triangular G f data]

theorem antipodal_anchor {α : Type*} [Fintype α] (G : α → TriangleGeometry)
    {n : ℕ} {L : ℕ → Line ℝ} (f : UpperFan.Sectors n 3 L) (data : FullData G f) :
    ∃ a : ZMod (2*3), f.ordinaryShared={a,a+3} := by
  classical
  have sep (z : ZMod (2*3)) (hz : z∈f.ordinaryShared) : z+1∉f.ordinaryShared := by
    intro hn
    obtain ⟨j,hj⟩ := f.no_run (by decide) z
    have hjv : j.val=0 ∨ j.val=1 := by have := j.isLt; omega
    rcases hjv with hjv|hjv
    · simp only [hjv,Nat.cast_zero,add_zero] at hj
      exact hj hz
    · simp only [hjv,Nat.cast_one] at hj
      exact hj hn
  by_contra no
  obtain ⟨z,hzo,hp,hn⟩ := UpperOpenMathMarkedCurvatureWeights.finite_two_cap_non_antipodal_mark
    f.ordinaryShared data.ordinary_card sep no
  have hz : z∈f.coreShared := by
    rw [UpperFan.Sectors.coreShared]
    exact mem_sdiff.mpr ⟨by rw [full_shared G f data]; simp,hzo⟩
  exact data.no_mark z hz ⟨hp,hn⟩

theorem shifted_full_data {α : Type*} [Fintype α] (G : α → TriangleGeometry)
    {n : ℕ} {L : ℕ → Line ℝ} (f : UpperFan.Sectors n 3 L)
    (data : FullData G f) (a : ZMod (2*3)) :
    FullData G (UpperOpenMathRotation.Sectors.shift f a) := by
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
    obtain ⟨o⟩ := data.occurrences (a+z)
      ((UpperOpenMathRotation.Sectors.shift_mem_triangular f a z).mp hz)
    exact ⟨{
      index := o.index, triangle := o.triangle, transport := o.transport
      center := o.center, left := o.left
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
    {n : ℕ} {L : ℕ → Line ℝ} (f : UpperFan.Sectors n 3 L) (data : FullData G f) :
    ∃ g : UpperFan.Sectors n 3 L, g.center=f.center ∧ AntipodalData G g := by
  classical
  obtain ⟨a,ha⟩ := antipodal_anchor G f data
  let g := UpperOpenMathRotation.Sectors.shift f a
  have dg := shifted_full_data G f data a
  have oge : g.ordinaryShared={0,3} := by
    ext z
    rw [UpperOpenMathRotation.Sectors.shift_mem_ordinaryShared,ha]
    simp only [mem_insert,mem_singleton]
    have eqzero : a+z=a ↔ z=0 := by
      constructor
      · intro hh
        exact add_left_cancel (by simpa only [add_zero] using hh : a+z=a+0)
      · intro hh
        simp only [hh,add_zero]
    rw [eqzero,add_right_inj]
  have cge : g.coreShared={1,2,4,5} := by
    rw [UpperFan.Sectors.coreShared,full_shared G g dg,oge]
    decide
  exact ⟨g,rfl,⟨dg,oge,cge,full_triangular G g dg⟩⟩

theorem lift_three {α : Type*} [Fintype α] (G : α → TriangleGeometry)
    {n r : ℕ} [NeZero (2*r)] {L : ℕ → Line ℝ} (hr : r=3)
    (f : UpperFan.Sectors n r L)
    (inj : Function.Injective f.point) (nc : ∀ z, f.point z≠f.center)
    (pos : ∀ z, 0<areaDet f.center (f.point z) (f.point (z+1)))
    (ord : f.ordinaryShared.card=2) (cor : f.coreShared.card=4)
    (ce : ∀ z∈f.coreShared, f.point z∈core n L)
    (im : f.coreShared.image (fun z => ({f.center,f.point z} : Edge))=
      (twoCoreEdges n L G).filter (fun e => f.center∈e))
    (occ : ∀ z∈f.triangular, Nonempty (UpperOpenMathSectorRecords.Occurrence G f.center f.point z))
    (nm : ∀ z∈f.coreShared, ¬(z-1∈f.ordinaryShared ∧ z+1∈f.ordinaryShared)) :
    ∃ g : UpperFan.Sectors n 3 L, g.center=f.center ∧ FullData G g := by
  subst r
  exact ⟨f,rfl,⟨inj,nc,pos,ord,cor,ce,im,occ,nm⟩⟩

theorem certificate_antipodal_chart {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (c : Point) (hc : c∈core n L) (rc : (supports n L c).card=3)
    (ac : ordinaryDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) c=2)
    (dc : coreDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) c=4)
    (zero : markedCount n L hL hn tri ht c=0) :
    ∃ f : UpperFan.Sectors n 3 L, f.center=c ∧
      AntipodalData (fun a => ofPredicate n L (tri a) hL (ht a)) f := by
  classical
  let G := fun a => ofPredicate n L (tri a) hL (ht a)
  letI : NeZero (2*(supports n L c).card) := ⟨by omega⟩
  let D := atPoint n L hL hn c
  let f := atCoreFan n L hL hn tri ht c hc
  have ord : f.ordinaryShared.card=2 := (at_core_ordinary_card n L hL hn tri hi ht c hc).trans ac
  have cor : f.coreShared.card=4 := (at_core_core_card n L hL hn tri hi ht c hc).trans dc
  have ce : ∀ z∈f.coreShared, f.point z∈core n L :=
    fan_core_endpoint n L hL hn tri ht c (mem_filter.mp hc).1 D (by omega) hi hc
  have im : f.coreShared.image (fun z => ({f.center,f.point z} : Edge))=
      (twoCoreEdges n L G).filter (fun e => f.center∈e) :=
    fan_core_image n L hL hn tri ht c (mem_filter.mp hc).1 D (by omega) hi hc
  have occ : ∀ z∈f.triangular, Nonempty (UpperOpenMathSectorRecords.Occurrence G f.center f.point z) := by
    intro z hz
    exact (UpperOpenMathSectorRecords.mem_triangular G c f.point z).mp hz
  have nm : ∀ z∈f.coreShared, ¬(z-1∈f.ordinaryShared ∧ z+1∈f.ordinaryShared) :=
    zero_marked_count_no_mark n L hL hn tri hi ht c hc zero
  obtain ⟨g,hg,dg⟩ := lift_three G rc f
    (fan_point_injective n L hL hn tri ht c (mem_filter.mp hc).1 D (by omega))
    (fan_point_ne_center n L hL hn tri ht c (mem_filter.mp hc).1 D (by omega))
    (fan_positive n L hL hn tri ht c (mem_filter.mp hc).1 D (by omega))
    ord cor ce im occ nm
  obtain ⟨h,hh,dh⟩ := normalized_exists G g dg
  exact ⟨h,hh.trans hg,dh⟩

#print axioms certificate_antipodal_chart

theorem core_edge_of_label {α : Type*} [Fintype α] (G : α → TriangleGeometry)
    {n : ℕ} {L : ℕ → Line ℝ} (f : UpperFan.Sectors n 3 L) (data : FullData G f)
    (z : ZMod (2*3)) (hz : z∈f.coreShared) :
    {f.center,f.point z}∈twoCoreEdges n L G := by
  classical
  have hm : ({f.center,f.point z} : Edge)∈f.coreShared.image
      (fun z => ({f.center,f.point z} : Edge)) := mem_image.mpr ⟨z,hz,rfl⟩
  rw [data.core_image] at hm
  exact (mem_filter.mp hm).1

theorem star_card {α : Type*} [Fintype α] (G : α → TriangleGeometry)
    {n : ℕ} {L : ℕ → Line ℝ} (f : UpperFan.Sectors n 3 L) (data : FullData G f) :
    (insert f.center (f.coreShared.image f.point)).card=5 := by
  classical
  have no : f.center∉f.coreShared.image f.point := by
    intro h
    obtain ⟨z,_,hz⟩ := mem_image.mp h
    exact data.noncentral z hz
  rw [card_insert_of_notMem no,card_image_of_injective _ data.injective,data.core_card]

theorem closed_star_eq {α : Type*} [Fintype α] (G : α → TriangleGeometry)
    {n : ℕ} {L : ℕ → Line ℝ} (f : UpperFan.Sectors n 3 L) (data : FullData G f)
    (P : Finset Point) (hc : f.center∈P) (small : P.card≤5)
    (closed : UpperOpenMathCoreComponents.SharedCoreClosed n L G P) :
    P=insert f.center (f.coreShared.image f.point) := by
  classical
  apply Eq.symm
  apply eq_of_subset_of_card_le
  · intro p hp
    rcases mem_insert.mp hp with hp|hp
    · simpa only [hp] using hc
    · obtain ⟨z,hz,rfl⟩ := mem_image.mp hp
      exact closed {f.center,f.point z} (core_edge_of_label G f data z hz)
        f.center (by simp) hc (by simp)
  · rw [star_card G f data]
    exact small

#print axioms closed_star_eq

theorem shift_three_data {α : Type*} [Fintype α] (G : α → TriangleGeometry)
    {n : ℕ} {L : ℕ → Line ℝ} (f : UpperFan.Sectors n 3 L) (data : AntipodalData G f) :
    AntipodalData G (UpperOpenMathRotation.Sectors.shift f 3) := by
  classical
  have dg := shifted_full_data G f data.toFullData 3
  refine ⟨dg,?_,?_,full_triangular G _ dg⟩
  · ext z
    rw [UpperOpenMathRotation.Sectors.shift_mem_ordinaryShared,data.ordinary_eq]
    simp only [mem_insert,mem_singleton]
    exact (by decide : ∀ z : ZMod 6, 3+z=0 ∨ 3+z=3 ↔ z=0 ∨ z=3) z
  · ext z
    rw [UpperOpenMathRotation.Sectors.shift_mem_coreShared,data.core_eq]
    simp only [mem_insert,mem_singleton]
    exact (by decide : ∀ z : ZMod 6,
      3+z=1 ∨ 3+z=2 ∨ 3+z=4 ∨ 3+z=5 ↔ z=1 ∨ z=2 ∨ z=4 ∨ z=5) z

#print axioms shift_three_data
end Kobon.UpperOpenMathAntipodalTwoCapChart
