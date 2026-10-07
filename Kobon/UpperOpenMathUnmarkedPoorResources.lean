import Kobon.UpperOpenMathMarkedPorts

/-! Unmarked incidences reduce the actual capacity available to marked
ports. A low-cap core reaching every poor target reserves one flag each. -/
namespace Kobon.UpperOpenMathUnmarkedPoorResources
open Cells FanGeometry UpperVertexBudget UpperTriangleIncidence UpperSharedIncidence
  UpperCoreExtraction UpperOpenMathCapHeavyTriples UpperOpenMathCoreComponents
  UpperOpenMathActualFans UpperOpenMathMarkedPorts Finset
open scoped BigOperators
set_option maxHeartbeats 1000000

theorem pair_insert_injective (c : Point) : Function.Injective (fun p : Point => ({c,p} : Edge)) := by
  classical
  intro p q he
  change ({c,p} : Edge)={c,q} at he
  have hp : p∈({c,q} : Edge) := by rw [← he]; simp
  rcases mem_insert.mp hp with pc|pq
  · have hq : q∈({c,p} : Edge) := by rw [he]; simp
    have qc : q=c := by simpa only [pc,insert_eq_of_mem (mem_singleton_self c),mem_singleton] using hq
    exact pc.trans qc.symm
  · exact mem_singleton.mp pq

theorem certificate_marked_capacity_reserved {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (triples : ∀ p∈core n L, (supports n L p).card=3)
    (P : Finset Point) (sub : P⊆core n L)
    (closed : SharedCoreClosed n L (fun a => ofPredicate n L (tri a) hL (ht a)) P)
    (c : Point) (hc : c∈P)
    (low : ordinaryDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) c≤1)
    (notPoor : 2<ordinaryDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) c+
      coreDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) c)
    (reaches : ∀ b∈P.filter (fun p => ordinaryDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) p≤1 ∧
      ordinaryDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) p+
        coreDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) p≤2),
      {c,b}∈twoCoreEdges n L (fun a => ofPredicate n L (tri a) hL (ht a))) :
    let G := fun a => ofPredicate n L (tri a) hL (ht a)
    let B := P.filter (fun p => ordinaryDegree n L G p≤1 ∧ ordinaryDegree n L G p+coreDegree n L G p≤2)
    (∑ p∈P, markedCount n L hL hn tri ht p)+B.card≤∑ p∈B, coreDegree n L G p := by
  classical
  let G := fun a => ofPredicate n L (tri a) hL (ht a)
  let B := P.filter (fun p => ordinaryDegree n L G p≤1 ∧ ordinaryDegree n L G p+coreDegree n L G p≤2)
  let M := P.biUnion (markedEdges n L hL hn tri ht)
  let U := B.image (fun b => ({c,b} : Edge))
  change ordinaryDegree n L G c≤1 at low
  have disjoint : (P : Set Point).PairwiseDisjoint (markedEdges n L hL hn tri ht) := by
    intro p hp q hq hpq
    apply disjoint_left.mpr
    intro e hep heq
    have sp := marked_edge_spec n L hL hn tri hi ht triples p (sub hp) e hep
    have sq := marked_edge_spec n L hL hn tri hi ht triples q (sub hq) e heq
    have lo := (mem_filter.mp (sp.2.2.2 q sq.2.1 (Ne.symm hpq))).2.2.1
    have high := sq.2.2.1
    omega
  have sumMarks : (∑ p∈P, markedCount n L hL hn tri ht p)=M.card := by
    rw [card_biUnion disjoint]
    rfl
  have mSub : M⊆twoCoreEdges n L G := by
    intro e he
    obtain ⟨p,hp,hep⟩ := mem_biUnion.mp he
    exact (marked_edge_spec n L hL hn tri hi ht triples p (sub hp) e hep).1
  have uSub : U⊆twoCoreEdges n L G := by
    intro e he
    obtain ⟨b,hb,rfl⟩ := mem_image.mp he
    exact reaches b hb
  have separated : Disjoint M U := by
    apply disjoint_left.mpr
    intro e hm hu
    obtain ⟨p,hp,hep⟩ := mem_biUnion.mp hm
    obtain ⟨b,hb,he⟩ := mem_image.mp hu
    have source := (marked_edge_spec n L hL hn tri hi ht triples p (sub hp) e hep).2.1
    rw [← he] at source
    rcases mem_insert.mp source with pc|pb
    · have high := (marked_edge_spec n L hL hn tri hi ht triples p (sub hp) e hep).2.2.1
      change 2≤ordinaryDegree n L G p at high
      rw [pc] at high
      omega
    · have high := (marked_edge_spec n L hL hn tri hi ht triples p (sub hp) e hep).2.2.1
      change 2≤ordinaryDegree n L G p at high
      have blo := (mem_filter.mp hb).2.1
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
    have qB : q∈B := mem_filter.mpr ⟨qP,(mem_filter.mp poor).2.2⟩
    exact card_pos.mpr ⟨q,mem_inter.mpr ⟨hqe,qB⟩⟩
  have positiveU (e : Edge) (he : e∈U) : 1≤(e∩B).card := by
    obtain ⟨b,hb,rfl⟩ := mem_image.mp he
    exact card_pos.mpr ⟨b,mem_inter.mpr ⟨by simp,hb⟩⟩
  have uCard : U.card=B.card := card_image_of_injective B (pair_insert_injective c)
  have count : M.card+B.card≤∑ e∈twoCoreEdges n L G, (e∩B).card := by
    calc
      _=(M∪U).card := by rw [card_union_of_disjoint separated,uCard]
      _=∑ _e∈M∪U, 1 := by simp
      _≤∑ e∈M∪U, (e∩B).card := sum_le_sum (fun e he => by
        rcases mem_union.mp he with hm|hu
        · exact positiveM e hm
        · exact positiveU e hu)
      _≤∑ e∈twoCoreEdges n L G, (e∩B).card :=
        sum_le_sum_of_subset_of_nonneg (union_subset mSub uSub) (fun _ _ _ => Nat.zero_le _)
  rw [← UpperOpenMathCoreDoubleCount.endpoint_double_count] at count
  change (∑ p∈P, markedCount n L hL hn tri ht p)+B.card≤∑ p∈B, coreDegree n L G p
  rw [sumMarks]
  exact count

#print axioms certificate_marked_capacity_reserved
end Kobon.UpperOpenMathUnmarkedPoorResources
