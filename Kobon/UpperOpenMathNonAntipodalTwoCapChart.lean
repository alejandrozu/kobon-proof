import Kobon.UpperOpenMathFullTripleChart
import Kobon.UpperOpenMathAntipodalStarDegree

/-! Source-preserving normalized charts for marked full two-cap triple fans.
The unique marked ray is indexed1 and the two ordinary rays0,2. -/
namespace Kobon.UpperOpenMathNonAntipodalTwoCapChart
open Cells FanGeometry UpperFan UpperVertexBudget UpperTriangleIncidence UpperSharedIncidence
  UpperCoreExtraction UpperOpenMathCapHeavyTriples UpperOpenMathActualFans
  UpperOpenMathRadialOrder UpperOpenMathMarkedPorts UpperOpenMathFullTripleChart Finset

structure NonAntipodalData {α : Type*} [Fintype α] (G : α → TriangleGeometry)
    {n : ℕ} {L : ℕ → Line ℝ} (f : UpperFan.Sectors n 3 L) : Prop
    extends FullOriginalData G f where
  ordinary_eq : f.ordinaryShared={0,2}
  core_eq : f.coreShared={1,3,4,5}

theorem shifted_full_original_data {α : Type*} [Fintype α] (G : α → TriangleGeometry)
    {n : ℕ} {L : ℕ → Line ℝ} (f : UpperFan.Sectors n 3 L)
    (data : FullOriginalData G f) (a : ZMod (2*3)) :
    FullOriginalData G (UpperOpenMathRotation.Sectors.shift f a) := by
  classical
  let g := UpperOpenMathRotation.Sectors.shift f a
  refine ⟨?_,?_,UpperOpenMathRotation.Sectors.shift_positive f data.positive a,?_,?_,?_,?_⟩
  · intro x y eq
    exact add_left_cancel (data.injective eq)
  · intro z
    exact data.noncentral (a+z)
  · intro z hz
    exact data.core_endpoint (a+z) ((UpperOpenMathRotation.Sectors.shift_mem_coreShared f a z).mp hz)
  · change g.coreShared.image (fun z => ({g.center,g.point z} : Edge))=
      (twoCoreEdges n L G).filter (fun e => f.center∈e)
    rw [← data.core_image]
    ext e
    constructor
    · intro he
      obtain ⟨z,hz,eq⟩ := mem_image.mp he
      exact mem_image.mpr ⟨a+z,(UpperOpenMathRotation.Sectors.shift_mem_coreShared f a z).mp hz,eq⟩
    · intro he
      obtain ⟨z,hz,eq⟩ := mem_image.mp he
      have cancel : a+(z-a)=z := by ring
      refine mem_image.mpr ⟨z-a,?_,?_⟩
      · apply (UpperOpenMathRotation.Sectors.shift_mem_coreShared f a (z-a)).mpr
        simpa only [cancel] using hz
      · simpa only [g,UpperOpenMathRotation.Sectors.shift_center,
          UpperOpenMathRotation.Sectors.shift_point,cancel] using eq
  · intro z hz
    obtain ⟨o⟩ := data.occurrences (a+z)
      ((UpperOpenMathRotation.Sectors.shift_mem_triangular f a z).mp hz)
    exact ⟨{
      index := o.index, triangle := o.triangle, transport := o.transport
      center := o.center, left := o.left
      right := by simpa only [UpperOpenMathRotation.Sectors.shift_point,add_assoc] using o.right
    }⟩
  · apply eq_univ_iff_forall.mpr
    intro z
    exact (UpperOpenMathRotation.Sectors.shift_mem_triangular f a z).mpr (by rw [data.full]; simp)

theorem normalize_marked {α : Type*} [Fintype α] (G : α → TriangleGeometry)
    {n : ℕ} {L : ℕ → Line ℝ} (f : UpperFan.Sectors n 3 L)
    (data : FullOriginalData G f) (ord : f.ordinaryShared.card=2)
    (z : ZMod (2*3)) (prev : z-1∈f.ordinaryShared) (next : z+1∈f.ordinaryShared) :
    ∃ g : UpperFan.Sectors n 3 L, g.center=f.center ∧ NonAntipodalData G g := by
  classical
  have neq : z-1≠z+1 := UpperOpenMathMarkedPorts.triple_neighbors_ne z
  have eqO : f.ordinaryShared={z-1,z+1} := by
    apply Eq.symm
    apply eq_of_subset_of_card_le
    · intro x hx
      rcases mem_insert.mp hx with rfl|hx
      · exact prev
      · simpa only [mem_singleton.mp hx] using next
    · rw [card_pair neq,ord]
  let g := UpperOpenMathRotation.Sectors.shift f (z-1)
  have dg := shifted_full_original_data G f data (z-1)
  have oge : g.ordinaryShared={0,2} := by
    ext x
    rw [UpperOpenMathRotation.Sectors.shift_mem_ordinaryShared,eqO]
    simp only [mem_insert,mem_singleton]
    exact (by decide : ∀ z x : ZMod 6, z-1+x=z-1 ∨ z-1+x=z+1 ↔ x=0 ∨ x=2) z x
  have gfull : g.triangular=univ := dg.full
  have shared : g.shared=univ := by ext x; simp [UpperFan.Sectors.shared,gfull]
  have cge : g.coreShared={1,3,4,5} := by
    rw [UpperFan.Sectors.coreShared,shared,oge]
    decide
  exact ⟨g,rfl,⟨dg,oge,cge⟩⟩

theorem lift_marked_three {α : Type*} [Fintype α] (G : α → TriangleGeometry)
    {n r : ℕ} [NeZero (2*r)] {L : ℕ → Line ℝ} (hr : r=3)
    (f : UpperFan.Sectors n r L)
    (inj : Function.Injective f.point) (nc : ∀ z, f.point z≠f.center)
    (pos : ∀ z, 0<areaDet f.center (f.point z) (f.point (z+1)))
    (ord : f.ordinaryShared.card=2) (cor : f.coreShared.card=4)
    (ce : ∀ z∈f.coreShared, f.point z∈core n L)
    (im : f.coreShared.image (fun z => ({f.center,f.point z} : Edge))=
      (twoCoreEdges n L G).filter (fun e => f.center∈e))
    (occ : ∀ z∈f.triangular, Nonempty (UpperOpenMathSectorRecords.Occurrence G f.center f.point z))
    (z : ZMod (2*r)) (prev : z-1∈f.ordinaryShared) (next : z+1∈f.ordinaryShared) :
    ∃ g : UpperFan.Sectors n 3 L, g.center=f.center ∧ NonAntipodalData G g := by
  subst r
  have full : f.triangular=univ := by
    have split := f.shared_card_split
    rw [ord,cor] at split
    exact UpperOpenMathFullSharing.shared_full f (by omega)
  exact normalize_marked G f ⟨inj,nc,pos,ce,im,occ,full⟩ ord z prev next

theorem certificate_nonantipodal_chart {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (c : Point) (hc : c∈core n L) (rc : (supports n L c).card=3)
    (ac : ordinaryDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) c=2)
    (dc : coreDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) c=4)
    (marked : markedCount n L hL hn tri ht c≠0) :
    ∃ f : UpperFan.Sectors n 3 L, f.center=c ∧
      NonAntipodalData (fun a => ofPredicate n L (tri a) hL (ht a)) f := by
  classical
  let G := fun a => ofPredicate n L (tri a) hL (ht a)
  letI : NeZero (2*(supports n L c).card) := ⟨by omega⟩
  let D := atPoint n L hL hn c
  let f := atCoreFan n L hL hn tri ht c hc
  have ord : f.ordinaryShared.card=2 := (at_core_ordinary_card n L hL hn tri hi ht c hc).trans ac
  have cor : f.coreShared.card=4 := (at_core_core_card n L hL hn tri hi ht c hc).trans dc
  obtain ⟨e,he⟩ := card_pos.mp (Nat.pos_of_ne_zero marked)
  change e∈markedEdges n L hL hn tri ht c at he
  obtain ⟨z,hzc,hprev,hnext,eq⟩ := marked_edge_ray n L hL hn tri ht c hc e he
  have ce : ∀ z∈f.coreShared, f.point z∈core n L :=
    fan_core_endpoint n L hL hn tri ht c (mem_filter.mp hc).1 D (by omega) hi hc
  have im : f.coreShared.image (fun z => ({f.center,f.point z} : Edge))=
      (twoCoreEdges n L G).filter (fun e => f.center∈e) :=
    fan_core_image n L hL hn tri ht c (mem_filter.mp hc).1 D (by omega) hi hc
  have occ : ∀ z∈f.triangular, Nonempty (UpperOpenMathSectorRecords.Occurrence G f.center f.point z) := by
    intro z hz
    exact (UpperOpenMathSectorRecords.mem_triangular G c f.point z).mp hz
  exact lift_marked_three G rc f
    (fan_point_injective n L hL hn tri ht c (mem_filter.mp hc).1 D (by omega))
    (fan_point_ne_center n L hL hn tri ht c (mem_filter.mp hc).1 D (by omega))
    (fan_positive n L hL hn tri ht c (mem_filter.mp hc).1 D (by omega))
    ord cor ce im occ z hprev hnext

#print axioms certificate_nonantipodal_chart
end Kobon.UpperOpenMathNonAntipodalTwoCapChart
