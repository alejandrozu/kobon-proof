import Kobon.UpperOpenMathAntipodalTwoCapChart
import Kobon.UpperOpenMathVertexBlocks
import Kobon.UpperOpenMathCoreDegree

/-! Real segment blockers restrict every outer core of a five-point full
antipodal star to its center and its adjacent partner. -/
namespace Kobon.UpperOpenMathAntipodalStarDegree
open Cells FanGeometry UpperFan UpperVertexBudget UpperTriangleIncidence UpperSharedIncidence
  UpperCoreExtraction UpperOpenMathCapHeavyTriples UpperOpenMathCoreComponents
  UpperOpenMathAntipodalTwoCapChart UpperOpenMathVertexBlocks UpperOpenMathActualFans
  UpperCoreCombinatorics UpperEdgeInventory Finset

theorem occurrence_radial_used {α : Type*} [Fintype α] (G : α → TriangleGeometry)
    {n : ℕ} {L : ℕ → Line ℝ} (f : UpperFan.Sectors n 3 L) (data : FullData G f)
    (z : ZMod (2*3)) : {f.center,f.point z}∈usedEdges G := by
  classical
  obtain ⟨o⟩ := data.occurrences z (by rw [full_triangular G f data]; simp)
  have used := UpperOpenMathSectorRecords.transported_side_used G o.index o.triangle o.transport 0
  change ({o.triangle.p,o.triangle.q} : Edge)∈usedEdges G at used
  rw [o.center,o.left] at used
  exact used

theorem certificate_star_blocks {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L)
    (tri : α → Triple) (ht : ∀ a, TrianglePredicate n L (tri a))
    (f : UpperFan.Sectors n 3 L)
    (data : AntipodalData (fun a => ofPredicate n L (tri a) hL (ht a)) f) :
    let G := fun a => ofPredicate n L (tri a) hL (ht a)
    {f.point 1,f.point 4}∉usedEdges G ∧ {f.point 2,f.point 5}∉usedEdges G ∧
      {f.point 1,f.point 5}∉usedEdges G ∧ {f.point 2,f.point 4}∉usedEdges G := by
  classical
  let G := fun a => ofPredicate n L (tri a) hL (ht a)
  have centerVertex : f.center∈vertices n L :=
    certificate_side_vertices n L hL tri ht (occurrence_radial_used G f data.toFullData 0) (by simp)
  have tipVertex (z : ZMod (2*3)) : f.point z∈vertices n L :=
    certificate_side_vertices n L hL tri ht (occurrence_radial_used G f data.toFullData z) (by simp)
  have anti14 : ∃ t : ℝ, 0<t ∧ t<1 ∧ f.center=segmentPoint (f.point 1) (f.point 4) t := by
    obtain ⟨s,hs,he⟩ := f.antipodal 1
    change f.point (1+3)=(f.center.1-s*((f.point 1).1-f.center.1),
      f.center.2-s*((f.point 1).2-f.center.2)) at he
    have hi : (1 : ZMod (2*3))+3=4 := by decide
    rw [hi] at he
    exact antipodal_center_between f.center (f.point 1) (f.point 4) s hs he
  have anti25 : ∃ t : ℝ, 0<t ∧ t<1 ∧ f.center=segmentPoint (f.point 2) (f.point 5) t := by
    obtain ⟨s,hs,he⟩ := f.antipodal 2
    change f.point (2+3)=(f.center.1-s*((f.point 2).1-f.center.1),
      f.center.2-s*((f.point 2).2-f.center.2)) at he
    have hi : (2 : ZMod (2*3))+3=5 := by decide
    rw [hi] at he
    exact antipodal_center_between f.center (f.point 2) (f.point 5) s hs he
  have cap15 : ∃ t : ℝ, 0<t ∧ t<1 ∧ f.point 0=segmentPoint (f.point 1) (f.point 5) t := by
    have ordinary : OrdinaryAt n L (f.point 0) :=
      ((f.mem_ordinaryShared 0).mp (by rw [data.ordinary_eq]; simp)).2.2
    obtain ⟨t,ht0,ht1,he⟩ := ordinary_cap_between f data.triangular_eq data.positive 0 ordinary
    have hi : (0 : ZMod (2*3))-1=5 := by decide
    have hj : (0 : ZMod (2*3))+1=1 := by decide
    rw [hi,hj] at he
    refine ⟨1-t,by linarith,by linarith,?_⟩
    rw [he]
    apply Prod.ext <;> dsimp [segmentPoint] <;> ring
  have cap24 : ∃ t : ℝ, 0<t ∧ t<1 ∧ f.point 3=segmentPoint (f.point 2) (f.point 4) t := by
    have ordinary : OrdinaryAt n L (f.point 3) :=
      ((f.mem_ordinaryShared 3).mp (by rw [data.ordinary_eq]; simp)).2.2
    obtain ⟨t,ht0,ht1,he⟩ := ordinary_cap_between f data.triangular_eq data.positive 3 ordinary
    have hi : (3 : ZMod (2*3))-1=2 := by decide
    have hj : (3 : ZMod (2*3))+1=4 := by decide
    exact ⟨t,ht0,ht1,by simpa only [hi,hj] using he⟩
  exact ⟨certificate_vertex_blocks_used_edge n L hL tri ht _ _ _ centerVertex anti14,
    certificate_vertex_blocks_used_edge n L hL tri ht _ _ _ centerVertex anti25,
    certificate_vertex_blocks_used_edge n L hL tri ht _ _ _ (tipVertex 0) cap15,
    certificate_vertex_blocks_used_edge n L hL tri ht _ _ _ (tipVertex 3) cap24⟩

theorem two_neighbor_card_bound (p u v : Point) (E : Finset Edge)
    (pairs : ∀ e∈E, e.card=2 ∧ p∈e ∧ e⊆({p,u,v} : Finset Point)) : E.card≤2 := by
  classical
  have bound := UpperOpenMathCoreDegree.pair_inventory_degree_bound ({p,u,v} : Finset Point) E
    (fun e he => ⟨(pairs e he).1,(pairs e he).2.2⟩) p (by simp)
  have filterEq : E.filter (fun e => p∈e)=E := filter_eq_self.mpr (fun e he => (pairs e he).2.1)
  rw [filterEq] at bound
  have hc : ({p,u,v} : Finset Point).card≤3 := by
    have h1 := card_insert_le p ({u,v} : Finset Point)
    have h2 := card_insert_le u ({v} : Finset Point)
    simp only [card_singleton] at h2
    omega
  omega

theorem certificate_outer_degrees {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L)
    (tri : α → Triple) (ht : ∀ a, TrianglePredicate n L (tri a))
    (f : UpperFan.Sectors n 3 L)
    (data : AntipodalData (fun a => ofPredicate n L (tri a) hL (ht a)) f)
    (P : Finset Point) (hc : f.center∈P) (small : P.card≤5)
    (closed : SharedCoreClosed n L (fun a => ofPredicate n L (tri a) hL (ht a)) P) :
    ∀ z∈f.coreShared, coreDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) (f.point z)≤2 := by
  classical
  let G := fun a => ofPredicate n L (tri a) hL (ht a)
  have star := closed_star_eq G f data.toFullData P hc small closed
  have memStar (q : Point) (hq : q∈P) :
      q=f.center ∨ q=f.point 1 ∨ q=f.point 2 ∨ q=f.point 4 ∨ q=f.point 5 := by
    rw [star] at hq
    rcases mem_insert.mp hq with hq|hq
    · exact Or.inl hq
    · obtain ⟨z,hz,hzq⟩ := mem_image.mp hq
      rw [data.core_eq] at hz
      simp only [mem_insert,mem_singleton] at hz
      rcases hz with rfl|rfl|rfl|rfl <;> simp only [hzq,or_true,true_or]
  obtain ⟨block14,block25,block15,block24⟩ := certificate_star_blocks n L hL tri ht f data
  have degreeBound (z v : ZMod (2*3)) (hz : z∈f.coreShared)
      (allowed : ∀ q, q∈P → q≠f.point z →
        {f.point z,q}∈usedEdges G → q=f.center ∨ q=f.point v) : coreDegree n L G (f.point z)≤2 := by
    let E := (twoCoreEdges n L G).filter (fun e => f.point z∈e)
    change E.card≤2
    apply two_neighbor_card_bound (f.point z) f.center (f.point v) E
    intro e he
    obtain ⟨he,hze⟩ := mem_filter.mp he
    have used := (mem_filter.mp (mem_sdiff.mp he).1).1
    obtain ⟨q,hqne,heq⟩ := pair_of_card_two_of_mem e (f.point z) hze (used_edge_card G used)
    have hp : f.point z∈P := by rw [star]; exact mem_insert_of_mem (mem_image.mpr ⟨z,hz,rfl⟩)
    have hq : q∈P := closed e he (f.point z) hze hp (by rw [heq]; simp)
    have hused : {f.point z,q}∈usedEdges G := by simpa only [heq] using used
    obtain center|mate := allowed q hq hqne hused
    · refine ⟨used_edge_card G used,hze,?_⟩
      rw [heq,center]
      simp
    · refine ⟨used_edge_card G used,hze,?_⟩
      rw [heq,mate]
      simp
  intro z hz
  have zcase : z=1 ∨ z=2 ∨ z=4 ∨ z=5 := by
    simpa only [data.core_eq,mem_insert,mem_singleton] using hz
  rcases zcase with rfl|rfl|rfl|rfl
  · apply degreeBound 1 2 hz
    intro q hq hn used
    rcases memStar q hq with h|h|h|h|h
    · exact Or.inl h
    · exact False.elim (hn h)
    · exact Or.inr h
    · exact False.elim (block14 (by simpa only [h] using used))
    · exact False.elim (block15 (by simpa only [h] using used))
  · apply degreeBound 2 1 hz
    intro q hq hn used
    rcases memStar q hq with h|h|h|h|h
    · exact Or.inl h
    · exact Or.inr h
    · exact False.elim (hn h)
    · exact False.elim (block24 (by simpa only [h] using used))
    · exact False.elim (block25 (by simpa only [h] using used))
  · apply degreeBound 4 5 hz
    intro q hq hn used
    rcases memStar q hq with h|h|h|h|h
    · exact Or.inl h
    · exact False.elim (block14 (by simpa only [h,pair_comm] using used))
    · exact False.elim (block24 (by simpa only [h,pair_comm] using used))
    · exact False.elim (hn h)
    · exact Or.inr h
  · apply degreeBound 5 4 hz
    intro q hq hn used
    rcases memStar q hq with h|h|h|h|h
    · exact Or.inl h
    · exact False.elim (block15 (by simpa only [h,pair_comm] using used))
    · exact False.elim (block25 (by simpa only [h,pair_comm] using used))
    · exact Or.inr h
    · exact False.elim (hn h)

#print axioms certificate_star_blocks
#print axioms certificate_outer_degrees

theorem certificate_first_neighbors {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L)
    (tri : α → Triple) (ht : ∀ a, TrianglePredicate n L (tri a))
    (f : UpperFan.Sectors n 3 L)
    (data : AntipodalData (fun a => ofPredicate n L (tri a) hL (ht a)) f)
    (P : Finset Point) (hc : f.center∈P) (small : P.card≤5)
    (closed : SharedCoreClosed n L (fun a => ofPredicate n L (tri a) hL (ht a)) P) :
    let G := fun a => ofPredicate n L (tri a) hL (ht a)
    (∀ q, {f.point 1,q}∈twoCoreEdges n L G → q=f.center ∨ q=f.point 2) ∧
      (∀ q, {f.point 2,q}∈twoCoreEdges n L G → q=f.center ∨ q=f.point 1) := by
  classical
  let G := fun a => ofPredicate n L (tri a) hL (ht a)
  have star := closed_star_eq G f data.toFullData P hc small closed
  have memStar (q : Point) (hq : q∈P) :
      q=f.center ∨ q=f.point 1 ∨ q=f.point 2 ∨ q=f.point 4 ∨ q=f.point 5 := by
    rw [star] at hq
    rcases mem_insert.mp hq with hq|hq
    · exact Or.inl hq
    · obtain ⟨z,hz,hzq⟩ := mem_image.mp hq
      rw [data.core_eq] at hz
      simp only [mem_insert,mem_singleton] at hz
      rcases hz with rfl|rfl|rfl|rfl <;> simp only [hzq,or_true,true_or]
  obtain ⟨block14,block25,block15,block24⟩ := certificate_star_blocks n L hL tri ht f data
  have endpoint (z : ZMod (2*3)) (hz : z∈f.coreShared) (q : Point)
      (edge : {f.point z,q}∈twoCoreEdges n L G) : q∈P ∧ q≠f.point z ∧
        {f.point z,q}∈usedEdges G := by
    have used := (mem_filter.mp (mem_sdiff.mp edge).1).1
    have hp : f.point z∈P := by rw [star]; exact mem_insert_of_mem (mem_image.mpr ⟨z,hz,rfl⟩)
    have hq : q∈P := closed {f.point z,q} edge (f.point z) (by simp) hp (by simp)
    have ne : q≠f.point z := by
      intro he
      have count := used_edge_card G used
      simp only [he,insert_eq_of_mem (mem_singleton_self (f.point z)),card_singleton] at count
      omega
    exact ⟨hq,ne,used⟩
  constructor
  · intro q edge
    obtain ⟨hq,hn,used⟩ := endpoint 1 (by rw [data.core_eq]; simp) q edge
    rcases memStar q hq with h|h|h|h|h
    · exact Or.inl h
    · exact False.elim (hn h)
    · exact Or.inr h
    · exact False.elim (block14 (by simpa only [h] using used))
    · exact False.elim (block15 (by simpa only [h] using used))
  · intro q edge
    obtain ⟨hq,hn,used⟩ := endpoint 2 (by rw [data.core_eq]; simp) q edge
    rcases memStar q hq with h|h|h|h|h
    · exact Or.inl h
    · exact Or.inr h
    · exact False.elim (hn h)
    · exact False.elim (block24 (by simpa only [h] using used))
    · exact False.elim (block25 (by simpa only [h] using used))

#print axioms certificate_first_neighbors
end Kobon.UpperOpenMathAntipodalStarDegree
