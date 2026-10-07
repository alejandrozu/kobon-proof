import Kobon.UpperOpenMathUnmarkedPoorResources

/-! Arbitrary unmarked source sets reserve actual poor endpoint slots. -/
namespace Kobon.UpperOpenMathUnmarkedCrossResources
open Cells FanGeometry UpperVertexBudget UpperTriangleIncidence UpperSharedIncidence
  UpperCoreExtraction UpperOpenMathCapHeavyTriples UpperOpenMathCoreComponents
  UpperOpenMathActualFans UpperOpenMathMarkedPorts Finset
open scoped BigOperators
set_option maxHeartbeats 1000000

noncomputable def crossEdges {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (G : α → TriangleGeometry) (S B : Finset Point) : Finset Edge := by
  classical
  exact (twoCoreEdges n L G).filter (fun e => (e∩S).Nonempty ∧ (e∩B).Nonempty)

noncomputable def degreeFrom {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (G : α → TriangleGeometry) (S : Finset Point) (p : Point) : ℕ := by
  classical
  exact ((twoCoreEdges n L G).filter (fun e => p∈e ∧ (e∩S).Nonempty)).card

theorem degreeFrom_le {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (G : α → TriangleGeometry) (S : Finset Point) (p : Point) :
    degreeFrom n L G S p≤coreDegree n L G p := by
  classical
  apply card_le_card
  intro e he
  exact mem_filter.mpr ⟨(mem_filter.mp he).1,(mem_filter.mp he).2.1⟩

theorem degreeFrom_mono {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (G : α → TriangleGeometry) (S T : Finset Point)
    (sub : S⊆T) (p : Point) : degreeFrom n L G S p≤degreeFrom n L G T p := by
  classical
  apply card_le_card
  intro e he
  obtain ⟨he,hpe,q,hq⟩ := mem_filter.mp he
  obtain ⟨hqe,hqS⟩ := mem_inter.mp hq
  exact mem_filter.mpr ⟨he,hpe,⟨q,mem_inter.mpr ⟨hqe,sub hqS⟩⟩⟩

theorem cross_pair_of_card_two (e : Edge) (S B : Finset Point) (card : e.card=2)
    (disjoint : Disjoint S B) (left : (e∩S).Nonempty) (right : (e∩B).Nonempty) :
    ∃ s∈S, ∃ b∈B, s≠b ∧ e={s,b} := by
  classical
  obtain ⟨s,hs⟩ := left
  obtain ⟨b,hb⟩ := right
  obtain ⟨hse,hsS⟩ := mem_inter.mp hs
  obtain ⟨hbe,hbB⟩ := mem_inter.mp hb
  have ne : s≠b := by
    intro he
    exact disjoint_left.mp disjoint hsS (by simpa only [he] using hbB)
  refine ⟨s,hsS,b,hbB,ne,?_⟩
  apply Eq.symm
  apply eq_of_subset_of_card_le
  · intro p hp
    rcases mem_insert.mp hp with hp|hp
    · simpa only [hp] using hse
    · simpa only [mem_singleton.mp hp] using hbe
  · rw [card_pair ne,card]

theorem cross_endpoint_sum {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (G : α → TriangleGeometry) (S B : Finset Point)
    (disjoint : Disjoint S B) :
    (∑ b∈B, ((crossEdges n L G S B).filter (fun e => b∈e)).card)=(crossEdges n L G S B).card := by
  classical
  rw [UpperOpenMathCoreDoubleCount.endpoint_double_count]
  have each (e : Edge) (he : e∈crossEdges n L G S B) : (e∩B).card=1 := by
    obtain ⟨he,hs,hb⟩ := mem_filter.mp he
    have hc := used_edge_card G (mem_filter.mp (mem_sdiff.mp he).1).1
    obtain ⟨s,hs,b,hb,ne,pair⟩ := cross_pair_of_card_two e S B hc disjoint hs hb
    have sn : s∉B := fun h => disjoint_left.mp disjoint hs h
    rw [pair]
    simp [sn,hb]
  rw [sum_congr rfl each]
  simp

theorem degreeFrom_sum {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (G : α → TriangleGeometry) (S B : Finset Point)
    (disjoint : Disjoint S B) :
    (∑ b∈B, degreeFrom n L G S b)=(crossEdges n L G S B).card := by
  classical
  rw [← cross_endpoint_sum n L G S B disjoint]
  apply sum_congr rfl
  intro b hb
  apply congrArg Finset.card
  ext e
  constructor
  · intro he
    obtain ⟨heD,hbe,hS⟩ := mem_filter.mp he
    exact mem_filter.mpr ⟨mem_filter.mpr ⟨heD,hS,⟨b,mem_inter.mpr ⟨hbe,hb⟩⟩⟩,hbe⟩
  · intro he
    obtain ⟨heU,hbe⟩ := mem_filter.mp he
    obtain ⟨heD,hS,hB⟩ := mem_filter.mp heU
    exact mem_filter.mpr ⟨heD,hbe,hS⟩

theorem certificate_unmarked_cross_capacity {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (triples : ∀ p∈core n L, (supports n L p).card=3)
    (P S : Finset Point) (sub : P⊆core n L) (sSub : S⊆P)
    (closed : SharedCoreClosed n L (fun a => ofPredicate n L (tri a) hL (ht a)) P)
    (unmarked : ∀ s∈S, markedCount n L hL hn tri ht s=0)
    (notPoor : Disjoint S (P.filter (fun p => ordinaryDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) p≤1 ∧
      ordinaryDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) p+
        coreDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) p≤2))) :
    let G := fun a => ofPredicate n L (tri a) hL (ht a)
    let B := P.filter (fun p => ordinaryDegree n L G p≤1 ∧ ordinaryDegree n L G p+coreDegree n L G p≤2)
    (∑ p∈P, markedCount n L hL hn tri ht p)+(crossEdges n L G S B).card≤∑ p∈B, coreDegree n L G p := by
  classical
  let G := fun a => ofPredicate n L (tri a) hL (ht a)
  let B := P.filter (fun p => ordinaryDegree n L G p≤1 ∧ ordinaryDegree n L G p+coreDegree n L G p≤2)
  let M := P.biUnion (markedEdges n L hL hn tri ht)
  let U := crossEdges n L G S B
  have disjoint : (P : Set Point).PairwiseDisjoint (markedEdges n L hL hn tri ht) := by
    intro p hp q hq hpq
    apply disjoint_left.mpr
    intro e hep heq
    have sp := marked_edge_spec n L hL hn tri hi ht triples p (sub hp) e hep
    have sq := marked_edge_spec n L hL hn tri hi ht triples q (sub hq) e heq
    have lo := (mem_filter.mp (sp.2.2.2 q sq.2.1 (Ne.symm hpq))).2.2.1
    have high := sq.2.2.1
    omega
  have sumMarks : (∑ p∈P, markedCount n L hL hn tri ht p)=M.card := by rw [card_biUnion disjoint]; rfl
  have mSub : M⊆twoCoreEdges n L G := by
    intro e he
    obtain ⟨p,hp,hep⟩ := mem_biUnion.mp he
    exact (marked_edge_spec n L hL hn tri hi ht triples p (sub hp) e hep).1
  have uSub : U⊆twoCoreEdges n L G := filter_subset _ _
  have separated : Disjoint M U := by
    apply disjoint_left.mpr
    intro e hm hu
    obtain ⟨p,hp,hep⟩ := mem_biUnion.mp hm
    obtain ⟨he,hs,hb⟩ := mem_filter.mp hu
    have card := used_edge_card G (mem_filter.mp (mem_sdiff.mp he).1).1
    obtain ⟨s,hs,b,hb,ne,pair⟩ := cross_pair_of_card_two e S B card notPoor hs hb
    have source := (marked_edge_spec n L hL hn tri hi ht triples p (sub hp) e hep).2.1
    rw [pair] at source
    rcases mem_insert.mp source with ps|pb
    · have positive : 0<markedCount n L hL hn tri ht s := by
        apply card_pos.mpr
        exact ⟨e,by simpa only [ps] using hep⟩
      have zero := unmarked s hs
      omega
    · have high : 2≤ordinaryDegree n L G p :=
        (marked_edge_spec n L hL hn tri hi ht triples p (sub hp) e hep).2.2.1
      have low := (mem_filter.mp hb).2.1
      rw [mem_singleton.mp pb] at high
      omega
  have positiveM (e : Edge) (he : e∈M) : 1≤(e∩B).card := by
    obtain ⟨p,hp,hep⟩ := mem_biUnion.mp he
    have sp := marked_edge_spec n L hL hn tri hi ht triples p (sub hp) e hep
    obtain ⟨q,hqp,hpair⟩ := pair_of_card_two_of_mem e p sp.2.1
      (used_edge_card G (mem_filter.mp (mem_sdiff.mp sp.1).1).1)
    have hqe : q∈e := by simp [hpair]
    have poor := sp.2.2.2 q hqe hqp
    have qP : q∈P := closed e sp.1 p sp.2.1 hp hqe
    exact card_pos.mpr ⟨q,mem_inter.mpr ⟨hqe,mem_filter.mpr ⟨qP,(mem_filter.mp poor).2.2⟩⟩⟩
  have positiveU (e : Edge) (he : e∈U) : 1≤(e∩B).card :=
    card_pos.mpr (mem_filter.mp he).2.2
  have count : M.card+U.card≤∑ e∈twoCoreEdges n L G, (e∩B).card := by
    calc
      _=(M∪U).card := (card_union_of_disjoint separated).symm
      _=∑ _e∈M∪U, 1 := by simp
      _≤∑ e∈M∪U, (e∩B).card := sum_le_sum (fun e he => by
        rcases mem_union.mp he with hm|hu
        · exact positiveM e hm
        · exact positiveU e hu)
      _≤∑ e∈twoCoreEdges n L G, (e∩B).card :=
        sum_le_sum_of_subset_of_nonneg (union_subset mSub uSub) (fun _ _ _ => Nat.zero_le _)
  rw [← UpperOpenMathCoreDoubleCount.endpoint_double_count] at count
  change (∑ p∈P, markedCount n L hL hn tri ht p)+U.card≤∑ p∈B, coreDegree n L G p
  rw [sumMarks]
  exact count

#print axioms cross_endpoint_sum
#print axioms degreeFrom_sum
#print axioms certificate_unmarked_cross_capacity
end Kobon.UpperOpenMathUnmarkedCrossResources
