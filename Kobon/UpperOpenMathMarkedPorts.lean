import Kobon.UpperOpenMathMixedDegreeThreeResources

/-! Actual marked-port sets and their globally injective edge budget. -/
namespace Kobon.UpperOpenMathMarkedPorts
open Cells FanGeometry UpperVertexBudget UpperTriangleIncidence UpperSharedIncidence
  UpperCoreExtraction UpperOpenMathCapHeavyTriples UpperOpenMathCoreComponents
  UpperOpenMathActualFans UpperOpenMathRadialOrder Finset
open scoped BigOperators

noncomputable def atCoreFan {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (ht : ∀ a, TrianglePredicate n L (tri a))
    (c : Point) (hc : c∈core n L) [NeZero (2*(supports n L c).card)] :
    UpperFan.Sectors n (supports n L c).card L :=
  fan n L hL hn tri ht c (UpperOpenMathActualMatching.core_vertex n L hc)
    (atPoint n L hL hn c) (by have := core_multiplicity n L hL hc; omega)

noncomputable def markedEdges {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (ht : ∀ a, TrianglePredicate n L (tri a))
    (c : Point) : Finset Edge := by
  classical
  by_cases hc : c∈core n L
  · have hr := core_multiplicity n L hL hc
    letI : NeZero (2*(supports n L c).card) := ⟨by omega⟩
    let f := atCoreFan n L hL hn tri ht c hc
    exact (f.coreShared.filter (fun z => z-1∈f.ordinaryShared ∧ z+1∈f.ordinaryShared)).image
      (fun z => ({c,f.point z} : Edge))
  · exact ∅

noncomputable def markedCount {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (ht : ∀ a, TrianglePredicate n L (tri a)) (c : Point) : ℕ :=
  (markedEdges n L hL hn tri ht c).card

theorem marked_edges_eq {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (ht : ∀ a, TrianglePredicate n L (tri a))
    (c : Point) (hc : c∈core n L) [NeZero (2*(supports n L c).card)] :
    let f := atCoreFan n L hL hn tri ht c hc
    markedEdges n L hL hn tri ht c=
      (f.coreShared.filter (fun z => z-1∈f.ordinaryShared ∧ z+1∈f.ordinaryShared)).image
        (fun z => ({c,f.point z} : Edge)) := by
  classical
  unfold markedEdges
  rw [dif_pos hc]

theorem marked_edge_ray {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (ht : ∀ a, TrianglePredicate n L (tri a))
    (c : Point) (hc : c∈core n L) [NeZero (2*(supports n L c).card)]
    (e : Edge) (he : e∈markedEdges n L hL hn tri ht c) :
    let f := atCoreFan n L hL hn tri ht c hc
    ∃ z : ZMod (2*(supports n L c).card), z∈f.coreShared ∧
      z-1∈f.ordinaryShared ∧ z+1∈f.ordinaryShared ∧ e={c,f.point z} := by
  classical
  rw [marked_edges_eq n L hL hn tri ht c hc] at he
  obtain ⟨z,hz,he⟩ := mem_image.mp he
  obtain ⟨hzc,hprev,hnext⟩ := mem_filter.mp hz
  exact ⟨z,hzc,hprev,hnext,he.symm⟩

theorem triple_neighbors_ne : ∀ z : ZMod 6, z-1≠z+1 := by decide

theorem at_core_ordinary_card {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (c : Point) (hc : c∈core n L) [NeZero (2*(supports n L c).card)] :
    (atCoreFan n L hL hn tri ht c hc).ordinaryShared.card=
      ordinaryDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) c := by
  classical
  exact fan_ordinary_card n L hL hn tri ht c (mem_filter.mp hc).1
    (atPoint n L hL hn c) (by have := core_multiplicity n L hL hc; omega) hi hc

theorem at_core_core_card {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (c : Point) (hc : c∈core n L) [NeZero (2*(supports n L c).card)] :
    (atCoreFan n L hL hn tri ht c hc).coreShared.card=
      coreDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) c := by
  classical
  exact fan_core_card n L hL hn tri ht c (mem_filter.mp hc).1
    (atPoint n L hL hn c) (by have := core_multiplicity n L hL hc; omega) hi hc

theorem marked_count_ray_card {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (c : Point) (hc : c∈core n L) [NeZero (2*(supports n L c).card)] :
    let f := atCoreFan n L hL hn tri ht c hc
    markedCount n L hL hn tri ht c=
      (f.coreShared.filter (fun z => z-1∈f.ordinaryShared ∧ z+1∈f.ordinaryShared)).card := by
  classical
  rw [markedCount,marked_edges_eq n L hL hn tri ht c hc]
  apply card_image_of_injective
  exact pair_map_injective c _
    (fan_point_injective n L hL hn tri ht c (mem_filter.mp hc).1 (atPoint n L hL hn c)
      (by have := core_multiplicity n L hL hc; omega))
    (fan_point_ne_center n L hL hn tri ht c (mem_filter.mp hc).1 (atPoint n L hL hn c)
      (by have := core_multiplicity n L hL hc; omega))

theorem marked_count_of_extremal_triple {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (c : Point) (hc : c∈core n L) (rc : (supports n L c).card=3)
    (ac : ordinaryDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) c=3) :
    markedCount n L hL hn tri ht c=3 := by
  classical
  letI : NeZero (2*(supports n L c).card) := ⟨by omega⟩
  let f := atCoreFan n L hL hn tri ht c hc
  have fo : f.ordinaryShared.card=3 := (at_core_ordinary_card n L hL hn tri hi ht c hc).trans ac
  have fc : f.coreShared.card=3 := by
    rw [at_core_core_card n L hL hn tri hi ht c hc]
    apply UpperOpenMathSupportedCores.certificate_extremal_neighbor_count n L hL hn tri hi ht c hc
    change 2*(supports n L c).card-3≤ordinaryDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) c
    rw [rc,ac]
  have allMarked : f.coreShared.filter (fun z => z-1∈f.ordinaryShared ∧ z+1∈f.ordinaryShared)=f.coreShared := by
    apply filter_eq_self.mpr
    intro z hz
    exact UpperOpenMathMarkedPoverty.ordinary_neighbors_of_extremal_card rc f (by omega) z hz
  rw [marked_count_ray_card n L hL hn tri hi ht c hc,allMarked,fc]

theorem marked_count_of_partial_triple {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (c : Point) (hc : c∈core n L) (rc : (supports n L c).card=3)
    (ac : ordinaryDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) c=2)
    (dc : coreDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) c=1) :
    markedCount n L hL hn tri ht c=1 := by
  classical
  letI : NeZero (2*(supports n L c).card) := ⟨by omega⟩
  let f := atCoreFan n L hL hn tri ht c hc
  have fo : f.ordinaryShared.card=2 := (at_core_ordinary_card n L hL hn tri hi ht c hc).trans ac
  have fc : f.coreShared.card=1 := (at_core_core_card n L hL hn tri hi ht c hc).trans dc
  have allMarked : f.coreShared.filter (fun z => z-1∈f.ordinaryShared ∧ z+1∈f.ordinaryShared)=f.coreShared := by
    apply filter_eq_self.mpr
    intro z hz
    exact UpperOpenMathMarkedPoverty.ordinary_neighbors_of_two_one_card rc f fo fc z hz
  rw [marked_count_ray_card n L hL hn tri hi ht c hc,allMarked,fc]

theorem zero_marked_count_no_mark {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (c : Point) (hc : c∈core n L) [NeZero (2*(supports n L c).card)]
    (zero : markedCount n L hL hn tri ht c=0) :
    let f := atCoreFan n L hL hn tri ht c hc
    ∀ z∈f.coreShared, ¬(z-1∈f.ordinaryShared ∧ z+1∈f.ordinaryShared) := by
  classical
  let f := atCoreFan n L hL hn tri ht c hc
  have hc0 : (f.coreShared.filter (fun z => z-1∈f.ordinaryShared ∧ z+1∈f.ordinaryShared)).card=0 := by
    rw [← marked_count_ray_card n L hL hn tri hi ht c hc]
    exact zero
  have hempty := card_eq_zero.mp hc0
  change ∀ z∈f.coreShared, ¬(z-1∈f.ordinaryShared ∧ z+1∈f.ordinaryShared)
  intro z hz hm
  have hmem : z∈f.coreShared.filter (fun z => z-1∈f.ordinaryShared ∧ z+1∈f.ordinaryShared) :=
    mem_filter.mpr ⟨hz,hm⟩
  rw [hempty] at hmem
  exact notMem_empty z hmem

theorem certificate_normalized_two_two_of_zero_marks {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (c : Point) (hc : c∈core n L) (rc : (supports n L c).card=3)
    (ac : ordinaryDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) c=2)
    (dc : coreDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) c=2)
    (zero : markedCount n L hL hn tri ht c=0) :
    ∃ f : UpperFan.Sectors n 3 L, f.center=c ∧
      UpperOpenMathTripleCharts.NormalizedData (fun a => ofPredicate n L (tri a) hL (ht a)) f := by
  classical
  let G := fun a => ofPredicate n L (tri a) hL (ht a)
  letI : NeZero (2*(supports n L c).card) := ⟨by omega⟩
  let D := atPoint n L hL hn c
  let f := atCoreFan n L hL hn tri ht c hc
  have ord : f.ordinaryShared.card=2 := (at_core_ordinary_card n L hL hn tri hi ht c hc).trans ac
  have cor : f.coreShared.card=2 := (at_core_core_card n L hL hn tri hi ht c hc).trans dc
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
    zero_marked_count_no_mark n L hL hn tri hi ht c hc zero
  obtain ⟨g,hg,dg⟩ := UpperOpenMathTripleCharts.lift_three G rc f
    (fan_point_injective n L hL hn tri ht c (mem_filter.mp hc).1 D (by omega))
    (fan_point_ne_center n L hL hn tri ht c (mem_filter.mp hc).1 D (by omega))
    (fan_positive n L hL hn tri ht c (mem_filter.mp hc).1 D (by omega))
    ord cor ce im occ nm
  obtain ⟨h,hh,dh⟩ := UpperOpenMathTripleCharts.normalized_exists G g dg
  exact ⟨h,hh.trans hg,dh⟩

theorem marked_edge_spec {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (triples : ∀ p∈core n L, (supports n L p).card=3)
    (c : Point) (hc : c∈core n L) (e : Edge) (he : e∈markedEdges n L hL hn tri ht c) :
    let G := fun a => ofPredicate n L (tri a) hL (ht a)
    e∈twoCoreEdges n L G ∧ c∈e ∧ 2≤ordinaryDegree n L G c ∧
      ∀ q∈e, q≠c → q∈UpperOpenMathMixedCapBudget.poorTripleCores n L G := by
  classical
  let G := fun a => ofPredicate n L (tri a) hL (ht a)
  have rc := triples c hc
  letI : NeZero (2*(supports n L c).card) := ⟨by omega⟩
  let D := atPoint n L hL hn c
  let f := atCoreFan n L hL hn tri ht c hc
  rw [marked_edges_eq n L hL hn tri ht c hc] at he
  obtain ⟨z,hz,rfl⟩ := mem_image.mp he
  obtain ⟨hzCore,hprev,hnext⟩ := mem_filter.mp hz
  have coreEdge := (fan_core_iff n L hL hn tri ht c (mem_filter.mp hc).1 D (by omega) hi hc z).mp hzCore
  have dn : ∀ w : ZMod (2*(supports n L c).card), w-1≠w+1 := by
    rw [rc]
    exact triple_neighbors_ne
  have pairOrd : ({z-1,z+1} : Finset (ZMod (2*(supports n L c).card)))⊆f.ordinaryShared := by
    intro w hw
    rcases mem_insert.mp hw with hw|hw
    · simpa only [hw] using hprev
    · simpa only [mem_singleton.mp hw] using hnext
  have aTwo := card_le_card pairOrd
  rw [card_pair (dn z)] at aTwo
  change 2≤(fan n L hL hn tri ht c (mem_filter.mp hc).1 D (by omega)).ordinaryShared.card at aTwo
  rw [fan_ordinary_card n L hL hn tri ht c (mem_filter.mp hc).1 D (by omega) hi hc] at aTwo
  refine ⟨coreEdge,by simp,aTwo,?_⟩
  intro q hq hne
  have qeq : q=f.point z := by
    rcases mem_insert.mp hq with hq|hq
    · exact False.elim (hne hq)
    · exact mem_singleton.mp hq
  subst q
  have hqCore := fan_core_endpoint n L hL hn tri ht c (mem_filter.mp hc).1 D (by omega) hi hc z hzCore
  have rq := triples (f.point z) hqCore
  letI : NeZero (2*(supports n L (f.point z)).card) := ⟨by omega⟩
  let E := atPoint n L hL hn (f.point z)
  let g := fan n L hL hn tri ht (f.point z) (mem_filter.mp hqCore).1 E (by omega)
  obtain ⟨w,gw,gp,right,left⟩ := UpperOpenMathActualMatching.certificate_neighbor_matching
    n L hL hn tri hi ht c (f.point z) hc hqCore D E (by omega) (by omega) z hzCore rfl
  have poor := UpperOpenMathMarkedPoverty.marked_neighbor_poverty_sum_card rc rq hL f g z w
    hprev hnext gw rfl gp right left
    (fan_positive n L hL hn tri ht c (mem_filter.mp hc).1 D (by omega))
  rw [fan_ordinary_card n L hL hn tri ht (f.point z) (mem_filter.mp hqCore).1 E (by omega) hi hqCore,
    fan_core_card n L hL hn tri ht (f.point z) (mem_filter.mp hqCore).1 E (by omega) hi hqCore] at poor
  exact mem_filter.mpr ⟨hqCore,rq,poor⟩

theorem closed_marked_port_budget {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (triples : ∀ p∈core n L, (supports n L p).card=3)
    (P : Finset Point) (sub : P⊆core n L)
    (closed : SharedCoreClosed n L (fun a => ofPredicate n L (tri a) hL (ht a)) P) :
    let G := fun a => ofPredicate n L (tri a) hL (ht a)
    (∑ p∈P, markedCount n L hL hn tri ht p)≤
      ∑ p∈P.filter (fun p => ordinaryDegree n L G p≤1 ∧
        ordinaryDegree n L G p+coreDegree n L G p≤2), coreDegree n L G p := by
  classical
  let G := fun a => ofPredicate n L (tri a) hL (ht a)
  let B := P.filter (fun p => ordinaryDegree n L G p≤1 ∧ ordinaryDegree n L G p+coreDegree n L G p≤2)
  let M := P.biUnion (markedEdges n L hL hn tri ht)
  have disjoint : (P : Set Point).PairwiseDisjoint (markedEdges n L hL hn tri ht) := by
    intro p hp q hq hpq
    apply disjoint_left.mpr
    intro e hep heq
    have sp := marked_edge_spec n L hL hn tri hi ht triples p (sub hp) e hep
    have sq := marked_edge_spec n L hL hn tri hi ht triples q (sub hq) e heq
    have poor := sp.2.2.2 q sq.2.1 (Ne.symm hpq)
    have low := (mem_filter.mp poor).2.2.1
    have high := sq.2.2.1
    omega
  have sumMarks : (∑ p∈P, markedCount n L hL hn tri ht p)=M.card := by
    rw [card_biUnion disjoint]
    rfl
  have mSub : M⊆twoCoreEdges n L G := by
    intro e he
    obtain ⟨p,hp,hep⟩ := mem_biUnion.mp he
    exact (marked_edge_spec n L hL hn tri hi ht triples p (sub hp) e hep).1
  have mPositive (e : Edge) (he : e∈M) : 1≤(e∩B).card := by
    obtain ⟨p,hp,hep⟩ := mem_biUnion.mp he
    have sp := marked_edge_spec n L hL hn tri hi ht triples p (sub hp) e hep
    obtain ⟨q,hqp,hpair⟩ := pair_of_card_two_of_mem e p sp.2.1
      (used_edge_card G (mem_filter.mp (mem_sdiff.mp sp.1).1).1)
    have hqe : q∈e := by simp [hpair]
    have poor := sp.2.2.2 q hqe hqp
    have qP : q∈P := closed e sp.1 p sp.2.1 hp hqe
    have qB : q∈B := mem_filter.mpr ⟨qP,(mem_filter.mp poor).2.2⟩
    exact card_pos.mpr ⟨q,mem_inter.mpr ⟨hqe,qB⟩⟩
  have count : M.card≤∑ e∈twoCoreEdges n L G, (e∩B).card := by
    calc
      _=∑ _e∈M, 1 := by simp
      _≤∑ e∈M, (e∩B).card := sum_le_sum mPositive
      _≤∑ e∈twoCoreEdges n L G, (e∩B).card :=
        sum_le_sum_of_subset_of_nonneg mSub (fun _ _ _ => Nat.zero_le _)
  rw [← UpperOpenMathCoreDoubleCount.endpoint_double_count] at count
  rw [sumMarks]
  exact count

theorem marked_count_zero_of_low {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (triples : ∀ p∈core n L, (supports n L p).card=3)
    (c : Point) (hc : c∈core n L)
    (low : ordinaryDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) c≤1) :
    markedCount n L hL hn tri ht c=0 := by
  classical
  have empty : markedEdges n L hL hn tri ht c=∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro e he
    have h := (marked_edge_spec n L hL hn tri hi ht triples c hc e he).2.2.1
    omega
  simp only [markedCount,empty,card_empty]

theorem tight_marked_edge_coverage {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (triples : ∀ p∈core n L, (supports n L p).card=3)
    (P : Finset Point) (sub : P⊆core n L)
    (closed : SharedCoreClosed n L (fun a => ofPredicate n L (tri a) hL (ht a)) P)
    (tight : (∑ p∈P, markedCount n L hL hn tri ht p)=
      ∑ p∈P.filter (fun p => ordinaryDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) p≤1 ∧
        ordinaryDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) p+
          coreDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) p≤2),
        coreDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) p) :
    let G := fun a => ofPredicate n L (tri a) hL (ht a)
    let B := P.filter (fun p => ordinaryDegree n L G p≤1 ∧ ordinaryDegree n L G p+coreDegree n L G p≤2)
    ∀ q∈B, ∀ e∈twoCoreEdges n L G, q∈e →
      ∃ p∈P, p≠q ∧ e∈markedEdges n L hL hn tri ht p := by
  classical
  let G := fun a => ofPredicate n L (tri a) hL (ht a)
  let B := P.filter (fun p => ordinaryDegree n L G p≤1 ∧ ordinaryDegree n L G p+coreDegree n L G p≤2)
  let M := P.biUnion (markedEdges n L hL hn tri ht)
  have disjoint : (P : Set Point).PairwiseDisjoint (markedEdges n L hL hn tri ht) := by
    intro p hp q hq hpq
    apply disjoint_left.mpr
    intro e hep heq
    have sp := marked_edge_spec n L hL hn tri hi ht triples p (sub hp) e hep
    have sq := marked_edge_spec n L hL hn tri hi ht triples q (sub hq) e heq
    have low := (mem_filter.mp (sp.2.2.2 q sq.2.1 (Ne.symm hpq))).2.2.1
    have high := sq.2.2.1
    omega
  have sumMarks : (∑ p∈P, markedCount n L hL hn tri ht p)=M.card := by rw [card_biUnion disjoint]; rfl
  have mSub : M⊆twoCoreEdges n L G := by
    intro e he
    obtain ⟨p,hp,hep⟩ := mem_biUnion.mp he
    exact (marked_edge_spec n L hL hn tri hi ht triples p (sub hp) e hep).1
  have each (e : Edge) (he : e∈M) : (e∩B).card=1 := by
    obtain ⟨p,hp,hep⟩ := mem_biUnion.mp he
    have sp := marked_edge_spec n L hL hn tri hi ht triples p (sub hp) e hep
    have pNotB : p∉B := by
      intro h
      have lo := (mem_filter.mp h).2.1
      have high : 2≤ordinaryDegree n L G p := sp.2.2.1
      omega
    obtain ⟨q,hqp,heq⟩ := pair_of_card_two_of_mem e p sp.2.1
      (used_edge_card G (mem_filter.mp (mem_sdiff.mp sp.1).1).1)
    have hqe : q∈e := by simp [heq]
    have poor := sp.2.2.2 q hqe hqp
    have qP : q∈P := closed e sp.1 p sp.2.1 hp hqe
    have qB : q∈B := mem_filter.mpr ⟨qP,(mem_filter.mp poor).2.2⟩
    rw [heq]
    simp [pNotB,qB]
  have mSum : (∑ e∈M, (e∩B).card)=M.card := by
    calc
      _=∑ _e∈M, 1 := sum_congr rfl each
      _=M.card := by simp
  have allSum : (∑ e∈twoCoreEdges n L G, (e∩B).card)=M.card := by
    rw [← UpperOpenMathCoreDoubleCount.endpoint_double_count,← sumMarks]
    exact tight.symm
  have split := sum_sdiff mSub (f:=fun e : Edge => (e∩B).card)
  have outsideZero : (∑ e∈twoCoreEdges n L G\M, (e∩B).card)=0 := by omega
  have outsideEach := (sum_eq_zero_iff_of_nonneg (fun e he => Nat.zero_le (e∩B).card)).mp outsideZero
  change ∀ q∈B, ∀ e∈twoCoreEdges n L G, q∈e → ∃ p∈P, p≠q ∧ e∈markedEdges n L hL hn tri ht p
  intro q hq e he hqe
  have eM : e∈M := by
    by_contra hnot
    have zero := outsideEach e (mem_sdiff.mpr ⟨he,hnot⟩)
    have pos := card_pos.mpr ⟨q,mem_inter.mpr ⟨hqe,hq⟩⟩
    omega
  obtain ⟨p,hp,hep⟩ := mem_biUnion.mp eM
  refine ⟨p,hp,?_,hep⟩
  intro heq
  have high : 2≤ordinaryDegree n L G p :=
    (marked_edge_spec n L hL hn tri hi ht triples p (sub hp) e hep).2.2.1
  have low := (mem_filter.mp hq).2.1
  rw [heq] at high
  omega

#print axioms marked_edge_spec
#print axioms closed_marked_port_budget
#print axioms marked_count_of_extremal_triple
#print axioms marked_count_of_partial_triple
#print axioms tight_marked_edge_coverage
#print axioms certificate_normalized_two_two_of_zero_marks
end Kobon.UpperOpenMathMarkedPorts
