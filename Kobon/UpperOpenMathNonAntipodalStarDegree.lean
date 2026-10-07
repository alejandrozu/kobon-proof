import Kobon.UpperOpenMathNonAntipodalTwoCapChart

/-! A marked full two-cap star has three blocked outer diagonals. In a
closed component of at most five cores, its marked endpoint has degree at
most one and each other endpoint has degree at most three. -/
namespace Kobon.UpperOpenMathNonAntipodalStarDegree
open Cells FanGeometry UpperFan UpperVertexBudget UpperTriangleIncidence UpperSharedIncidence
  UpperCoreExtraction UpperOpenMathCapHeavyTriples UpperOpenMathCoreComponents
  UpperOpenMathNonAntipodalTwoCapChart UpperOpenMathVertexBlocks UpperOpenMathActualFans
  UpperCoreCombinatorics UpperEdgeInventory Finset

theorem occurrence_radial_used {α : Type*} [Fintype α] (G : α → TriangleGeometry)
    {n : ℕ} {L : ℕ → Line ℝ} (f : UpperFan.Sectors n 3 L) (data : NonAntipodalData G f)
    (z : ZMod (2*3)) : {f.center,f.point z}∈usedEdges G := by
  classical
  obtain ⟨o⟩ := data.occurrences z (by rw [data.full]; simp)
  have used := UpperOpenMathSectorRecords.transported_side_used G o.index o.triangle o.transport 0
  change ({o.triangle.p,o.triangle.q} : Edge)∈usedEdges G at used
  rw [o.center,o.left] at used
  exact used

theorem core_edge_of_label {α : Type*} [Fintype α] (G : α → TriangleGeometry)
    {n : ℕ} {L : ℕ → Line ℝ} (f : UpperFan.Sectors n 3 L) (data : NonAntipodalData G f)
    (z : ZMod (2*3)) (hz : z∈f.coreShared) :
    {f.center,f.point z}∈twoCoreEdges n L G := by
  classical
  have hm : ({f.center,f.point z} : Edge)∈f.coreShared.image
      (fun z => ({f.center,f.point z} : Edge)) := mem_image.mpr ⟨z,hz,rfl⟩
  rw [data.core_image] at hm
  exact (mem_filter.mp hm).1

theorem closed_star_eq {α : Type*} [Fintype α] (G : α → TriangleGeometry)
    {n : ℕ} {L : ℕ → Line ℝ} (f : UpperFan.Sectors n 3 L) (data : NonAntipodalData G f)
    (P : Finset Point) (hc : f.center∈P) (small : P.card≤5)
    (closed : SharedCoreClosed n L G P) :
    P=insert f.center (f.coreShared.image f.point) := by
  classical
  have starCard : (insert f.center (f.coreShared.image f.point)).card=5 := by
    have no : f.center∉f.coreShared.image f.point := by
      intro h
      obtain ⟨z,_,hz⟩ := mem_image.mp h
      exact data.noncentral z hz
    rw [card_insert_of_notMem no,card_image_of_injective _ data.injective,data.core_eq]
    decide
  apply Eq.symm
  apply eq_of_subset_of_card_le
  · intro p hp
    rcases mem_insert.mp hp with hp|hp
    · simpa only [hp] using hc
    · obtain ⟨z,hz,rfl⟩ := mem_image.mp hp
      exact closed {f.center,f.point z} (core_edge_of_label G f data z hz)
        f.center (by simp) hc (by simp)
  · rw [starCard]
    exact small

theorem certificate_star_blocks {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L)
    (tri : α → Triple) (ht : ∀ a, TrianglePredicate n L (tri a))
    (f : UpperFan.Sectors n 3 L)
    (data : NonAntipodalData (fun a => ofPredicate n L (tri a) hL (ht a)) f) :
    let G := fun a => ofPredicate n L (tri a) hL (ht a)
    {f.point 1,f.point 4}∉usedEdges G ∧ {f.point 1,f.point 5}∉usedEdges G ∧
      {f.point 1,f.point 3}∉usedEdges G := by
  classical
  let G := fun a => ofPredicate n L (tri a) hL (ht a)
  have centerVertex : f.center∈vertices n L :=
    certificate_side_vertices n L hL tri ht (occurrence_radial_used G f data 0) (by simp)
  have tipVertex (z : ZMod (2*3)) : f.point z∈vertices n L :=
    certificate_side_vertices n L hL tri ht (occurrence_radial_used G f data z) (by simp)
  have anti14 : ∃ t : ℝ, 0<t ∧ t<1 ∧ f.center=segmentPoint (f.point 1) (f.point 4) t := by
    obtain ⟨s,hs,he⟩ := f.antipodal 1
    change f.point (1+3)=(f.center.1-s*((f.point 1).1-f.center.1),
      f.center.2-s*((f.point 1).2-f.center.2)) at he
    have hi : (1 : ZMod (2*3))+3=4 := by decide
    rw [hi] at he
    exact antipodal_center_between f.center (f.point 1) (f.point 4) s hs he
  have cap15 : ∃ t : ℝ, 0<t ∧ t<1 ∧ f.point 0=segmentPoint (f.point 1) (f.point 5) t := by
    have ordinary : OrdinaryAt n L (f.point 0) :=
      ((f.mem_ordinaryShared 0).mp (by rw [data.ordinary_eq]; simp)).2.2
    obtain ⟨t,ht0,ht1,he⟩ := ordinary_cap_between f data.full data.positive 0 ordinary
    have hi : (0 : ZMod (2*3))-1=5 := by decide
    have hj : (0 : ZMod (2*3))+1=1 := by decide
    rw [hi,hj] at he
    refine ⟨1-t,by linarith,by linarith,?_⟩
    rw [he]
    apply Prod.ext <;> dsimp [segmentPoint] <;> ring
  have cap13 : ∃ t : ℝ, 0<t ∧ t<1 ∧ f.point 2=segmentPoint (f.point 1) (f.point 3) t := by
    have ordinary : OrdinaryAt n L (f.point 2) :=
      ((f.mem_ordinaryShared 2).mp (by rw [data.ordinary_eq]; simp)).2.2
    obtain ⟨t,ht0,ht1,he⟩ := ordinary_cap_between f data.full data.positive 2 ordinary
    have hi : (2 : ZMod (2*3))-1=1 := by decide
    have hj : (2 : ZMod (2*3))+1=3 := by decide
    exact ⟨t,ht0,ht1,by simpa only [hi,hj] using he⟩
  exact ⟨certificate_vertex_blocks_used_edge n L hL tri ht _ _ _ centerVertex anti14,
    certificate_vertex_blocks_used_edge n L hL tri ht _ _ _ (tipVertex 0) cap15,
    certificate_vertex_blocks_used_edge n L hL tri ht _ _ _ (tipVertex 2) cap13⟩

theorem certificate_outer_degrees {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L)
    (tri : α → Triple) (ht : ∀ a, TrianglePredicate n L (tri a))
    (f : UpperFan.Sectors n 3 L)
    (data : NonAntipodalData (fun a => ofPredicate n L (tri a) hL (ht a)) f)
    (P : Finset Point) (hc : f.center∈P) (small : P.card≤5)
    (closed : SharedCoreClosed n L (fun a => ofPredicate n L (tri a) hL (ht a)) P) :
    coreDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) (f.point 1)≤1 ∧
      ∀ z∈f.coreShared, coreDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) (f.point z)≤3 := by
  classical
  let G := fun a => ofPredicate n L (tri a) hL (ht a)
  have star := closed_star_eq G f data P hc small closed
  have memStar (q : Point) (hq : q∈P) :
      q=f.center ∨ q=f.point 1 ∨ q=f.point 3 ∨ q=f.point 4 ∨ q=f.point 5 := by
    rw [star] at hq
    rcases mem_insert.mp hq with hq|hq
    · exact Or.inl hq
    · obtain ⟨z,hz,hzq⟩ := mem_image.mp hq
      rw [data.core_eq] at hz
      simp only [mem_insert,mem_singleton] at hz
      rcases hz with rfl|rfl|rfl|rfl <;> simp only [hzq,or_true,true_or]
  obtain ⟨block14,block15,block13⟩ := certificate_star_blocks n L hL tri ht f data
  have degreeBound (z : ZMod (2*3)) (hz : z∈f.coreShared) (S : Finset Point)
      (hzS : f.point z∈S) (k : ℕ) (card : S.card≤k+1)
      (allowed : ∀ q, q∈P → q≠f.point z → {f.point z,q}∈usedEdges G → q∈S) :
      coreDegree n L G (f.point z)≤k := by
    let E := (twoCoreEdges n L G).filter (fun e => f.point z∈e)
    have bound := UpperOpenMathCoreDegree.pair_inventory_degree_bound S E (by
      intro e he
      obtain ⟨he,hze⟩ := mem_filter.mp he
      have used := (mem_filter.mp (mem_sdiff.mp he).1).1
      obtain ⟨q,hqne,heq⟩ := pair_of_card_two_of_mem e (f.point z) hze (used_edge_card G used)
      have hp : f.point z∈P := by rw [star]; exact mem_insert_of_mem (mem_image.mpr ⟨z,hz,rfl⟩)
      have hq : q∈P := closed e he (f.point z) hze hp (by rw [heq]; simp)
      have hused : {f.point z,q}∈usedEdges G := by simpa only [heq] using used
      have hqS := allowed q hq hqne hused
      refine ⟨used_edge_card G used,?_⟩
      rw [heq]
      intro x hx
      rcases mem_insert.mp hx with rfl|hx
      · exact hzS
      · exact mem_singleton.mp hx ▸ hqS) (f.point z) hzS
    have eq : E.filter (fun e => f.point z∈e)=E := filter_eq_self.mpr (fun e he => (mem_filter.mp he).2)
    rw [eq] at bound
    change E.card≤k
    omega
  have smallOne : ({f.point 1,f.center} : Finset Point).card≤1+1 := by
    simpa only [card_singleton] using card_insert_le (f.point 1) ({f.center} : Finset Point)
  have one : coreDegree n L G (f.point 1)≤1 := by
    apply degreeBound 1 (by rw [data.core_eq]; simp) {f.point 1,f.center} (by simp) 1 smallOne
    intro q hq ne used
    rcases memStar q hq with eq|eq|eq|eq|eq
    · simp [eq]
    · exact False.elim (ne eq)
    · exact False.elim (block13 (by simpa only [eq] using used))
    · exact False.elim (block14 (by simpa only [eq] using used))
    · exact False.elim (block15 (by simpa only [eq] using used))
  have smallOther : ({f.center,f.point 3,f.point 4,f.point 5} : Finset Point).card≤3+1 := by
    have h1 := card_insert_le f.center ({f.point 3,f.point 4,f.point 5} : Finset Point)
    have h2 := card_insert_le (f.point 3) ({f.point 4,f.point 5} : Finset Point)
    have h3 : ({f.point 4,f.point 5} : Finset Point).card≤2 := by
      simpa only [card_singleton] using card_insert_le (f.point 4) ({f.point 5} : Finset Point)
    omega
  change coreDegree n L G (f.point 1)≤1 ∧ ∀ z∈f.coreShared, coreDegree n L G (f.point z)≤3
  refine ⟨one,?_⟩
  intro z hz
  have zcase : z=1 ∨ z=3 ∨ z=4 ∨ z=5 := by simpa only [data.core_eq,mem_insert,mem_singleton] using hz
  rcases zcase with rfl|rfl|rfl|rfl
  · omega
  · apply degreeBound 3 hz {f.center,f.point 3,f.point 4,f.point 5} (by simp) 3 smallOther
    intro q hq ne used
    rcases memStar q hq with eq|eq|eq|eq|eq
    · simp [eq]
    · exact False.elim (block13 (by simpa only [eq,pair_comm] using used))
    · simp [eq]
    · simp [eq]
    · simp [eq]
  · apply degreeBound 4 hz {f.center,f.point 3,f.point 4,f.point 5} (by simp) 3 smallOther
    intro q hq ne used
    rcases memStar q hq with eq|eq|eq|eq|eq
    · simp [eq]
    · exact False.elim (block14 (by simpa only [eq,pair_comm] using used))
    · simp [eq]
    · simp [eq]
    · simp [eq]
  · apply degreeBound 5 hz {f.center,f.point 3,f.point 4,f.point 5} (by simp) 3 smallOther
    intro q hq ne used
    rcases memStar q hq with eq|eq|eq|eq|eq
    · simp [eq]
    · exact False.elim (block15 (by simpa only [eq,pair_comm] using used))
    · simp [eq]
    · simp [eq]
    · simp [eq]

#print axioms certificate_star_blocks
#print axioms certificate_outer_degrees
end Kobon.UpperOpenMathNonAntipodalStarDegree
