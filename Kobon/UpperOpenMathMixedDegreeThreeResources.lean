import Kobon.UpperOpenMathClosedExtremal
import Kobon.UpperOpenMathMixedCapBudget
import Kobon.UpperOpenMathTripleDegreeThree

/-! Actual closed-set charging from extremal triples to mixed targets. -/
namespace Kobon.UpperOpenMathMixedDegreeThreeResources
open Cells FanGeometry UpperVertexBudget UpperTriangleIncidence UpperSharedIncidence
  UpperCoreExtraction UpperOpenMathCapHeavyTriples UpperOpenMathCoreComponents
  UpperOpenMathActualFans Finset
open scoped BigOperators

theorem closed_mixed_extremal_edge_injection {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (P : Finset Point) (sub : P⊆core n L)
    (closed : SharedCoreClosed n L (fun a => ofPredicate n L (tri a) hL (ht a)) P) :
    let G := fun a => ofPredicate n L (tri a) hL (ht a)
    let E := P.filter (fun p => (supports n L p).card=3 ∧ ordinaryDegree n L G p=3)
    let B := P.filter (fun p => (supports n L p).card=3 ∧ ordinaryDegree n L G p≤1 ∧
      ordinaryDegree n L G p+coreDegree n L G p≤2)
    let H := P.filter (fun p => 4≤(supports n L p).card)
    ∀ e∈twoCoreEdges n L G, (e∩E).card≤(e∩(B∪H)).card := by
  classical
  let G := fun a => ofPredicate n L (tri a) hL (ht a)
  let E := P.filter (fun p => (supports n L p).card=3 ∧ ordinaryDegree n L G p=3)
  let B := P.filter (fun p => (supports n L p).card=3 ∧ ordinaryDegree n L G p≤1 ∧
    ordinaryDegree n L G p+coreDegree n L G p≤2)
  let H := P.filter (fun p => 4≤(supports n L p).card)
  have hInd (e : Edge) (he : e∈twoCoreEdges n L G) : (e∩E).card≤1 := by
    apply card_le_one.mpr
    intro p hp q hq
    by_contra hpq
    obtain ⟨hpe,hpE⟩ := mem_inter.mp hp
    obtain ⟨hqe,hqE⟩ := mem_inter.mp hq
    obtain ⟨hpP,hpR,hpOrd⟩ := mem_filter.mp hpE
    obtain ⟨hqP,hqR,hqOrd⟩ := mem_filter.mp hqE
    have hpair : e={p,q} := by
      apply Eq.symm
      apply eq_of_subset_of_card_le
      · intro x hx
        rcases mem_insert.mp hx with hx|hx
        · simpa only [hx] using hpe
        · simpa only [mem_singleton.mp hx] using hqe
      · rw [card_pair hpq,used_edge_card G (mem_filter.mp (mem_sdiff.mp he).1).1]
    exact certificate_cap_heavy_not_adjacent n L hL hn tri hi ht p q (sub hpP) (sub hqP)
      ⟨hpR,Or.inl hpOrd⟩ ⟨hqR,Or.inl hqOrd⟩ (by simpa only [hpair] using he)
  change ∀ e∈twoCoreEdges n L G, (e∩E).card≤(e∩(B∪H)).card
  intro e he
  by_cases hempty : e∩E=∅
  · simp only [hempty,card_empty,Nat.zero_le]
  · obtain ⟨p,hp⟩ := nonempty_iff_ne_empty.mpr hempty
    obtain ⟨hpe,hpE⟩ := mem_inter.mp hp
    obtain ⟨hpP,hpR,hpOrd⟩ := mem_filter.mp hpE
    obtain ⟨q,hqp,heq⟩ := pair_of_card_two_of_mem e p hpe
      (used_edge_card G (mem_filter.mp (mem_sdiff.mp he).1).1)
    have hqe : q∈e := by simp [heq]
    have hqP : q∈P := closed e he p hpe hpP hqe
    have hqR := core_multiplicity n L hL (sub hqP)
    have hqTarget : q∈B∪H := by
      by_cases hr : (supports n L q).card=3
      · have poor := UpperOpenMathMarkedPoverty.certificate_extremal_neighbor_sum
          n L hL hn tri hi ht p q (sub hpP) (sub hqP) hpR hr hpOrd
          (by simpa only [heq] using he)
        exact mem_union.mpr (Or.inl (mem_filter.mpr ⟨hqP,hr,poor⟩))
      · exact mem_union.mpr (Or.inr (mem_filter.mpr ⟨hqP,by omega⟩))
    exact (hInd e he).trans (card_pos.mpr ⟨q,mem_inter.mpr ⟨hqe,hqTarget⟩⟩)

theorem closed_mixed_extremal_counts {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (P : Finset Point) (sub : P⊆core n L)
    (closed : SharedCoreClosed n L (fun a => ofPredicate n L (tri a) hL (ht a)) P) :
    let G := fun a => ofPredicate n L (tri a) hL (ht a)
    let E := P.filter (fun p => (supports n L p).card=3 ∧ ordinaryDegree n L G p=3)
    let B := P.filter (fun p => (supports n L p).card=3 ∧ ordinaryDegree n L G p≤1 ∧
      ordinaryDegree n L G p+coreDegree n L G p≤2)
    let H := P.filter (fun p => 4≤(supports n L p).card)
    (∑ p∈E, coreDegree n L G p)=3*E.card ∧
      3*E.card≤(∑ p∈B, coreDegree n L G p)+(∑ p∈H, coreDegree n L G p) := by
  classical
  let G := fun a => ofPredicate n L (tri a) hL (ht a)
  let E := P.filter (fun p => (supports n L p).card=3 ∧ ordinaryDegree n L G p=3)
  let B := P.filter (fun p => (supports n L p).card=3 ∧ ordinaryDegree n L G p≤1 ∧
    ordinaryDegree n L G p+coreDegree n L G p≤2)
  let H := P.filter (fun p => 4≤(supports n L p).card)
  have hE : (∑ p∈E, coreDegree n L G p)=3*E.card := by
    calc
      _=∑ _p∈E, 3 := by
        apply sum_congr rfl
        intro p hp
        obtain ⟨hpP,hpR,hpOrd⟩ := mem_filter.mp hp
        have hext : 2*(supports n L p).card-3≤ordinaryDegree n L G p := by rw [hpR,hpOrd]
        exact UpperOpenMathSupportedCores.certificate_extremal_neighbor_count
          n L hL hn tri hi ht p (sub hpP) hext
      _=3*E.card := by simp [Nat.mul_comm]
  have hCount : (∑ p∈E, coreDegree n L G p)≤∑ p∈B∪H, coreDegree n L G p := by
    change (∑ p∈E, ((twoCoreEdges n L G).filter (fun e => p∈e)).card)≤
      ∑ p∈B∪H, ((twoCoreEdges n L G).filter (fun e => p∈e)).card
    rw [UpperOpenMathCoreDoubleCount.endpoint_double_count,
      UpperOpenMathCoreDoubleCount.endpoint_double_count]
    exact sum_le_sum (closed_mixed_extremal_edge_injection n L hL hn tri hi ht P sub closed)
  have bhDisjoint : Disjoint B H := by
    apply disjoint_left.mpr
    intro p hpB hpH
    have hr3 := (mem_filter.mp hpB).2.1
    have hr4 := (mem_filter.mp hpH).2
    omega
  rw [hE,sum_union bhDisjoint] at hCount
  exact ⟨hE,hCount⟩

#print axioms closed_mixed_extremal_edge_injection
#print axioms closed_mixed_extremal_counts
end Kobon.UpperOpenMathMixedDegreeThreeResources
