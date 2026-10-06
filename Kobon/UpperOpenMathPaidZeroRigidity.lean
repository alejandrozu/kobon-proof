import Kobon.UpperOpenMathPaidZeroEscape
import Kobon.UpperOpenMathNormalizedActualFull

/-! The paid equality case has no balanced rigid core; every alternative
then belongs to the finite full-fan escape argument. -/
namespace Kobon.UpperOpenMathPaidZeroRigidity
open Cells FanGeometry UpperFan UpperVertexBudget UpperTriangleIncidence UpperSharedIncidence
  UpperCoreExtraction UpperOpenMathCapHeavyTriples UpperOpenMathCoreComponents
  UpperOpenMathMarkedPorts UpperOpenMathPaidZeroTypes Finset
open scoped BigOperators
set_option maxHeartbeats 1000000

theorem closed_paid_zero_no_rigid {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (triples : ∀ p∈core n L, (supports n L p).card=3)
    (P : Finset Point) (sub : P⊆core n L)
    (closed : SharedCoreClosed n L (fun a => ofPredicate n L (tri a) hL (ht a)) P)
    (tight : TightOn n L hL hn tri ht P)
    (types : ∀ p∈P, ZeroType
      (ordinaryDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) p)
      (coreDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) p)
      (markedCount n L hL hn tri ht p)) :
    ∀ p∈P, ¬(ordinaryDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) p=2 ∧
      coreDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) p=2 ∧ markedCount n L hL hn tri ht p=0) := by
  classical
  let G := fun a => ofPredicate n L (tri a) hL (ht a)
  let a := ordinaryDegree n L G
  let d := coreDegree n L G
  let m := markedCount n L hL hn tri ht
  let R := P.filter (fun p => a p=2 ∧ d p=2 ∧ m p=0)
  have noFull (p : Point) (hp : p∈P) (rigid : a p=2 ∧ d p=2 ∧ m p=0)
      (q : Point) (hq : q∈core n L) (edge : {p,q}∈twoCoreEdges n L G)
      (full : a q+d q=6) : False := by
    obtain ⟨f,fc,df⟩ := certificate_normalized_two_two_of_zero_marks n L hL hn tri hi ht
      p (sub hp) (triples p (sub hp)) rigid.1 rigid.2.1 rigid.2.2
    have neighbors (b : Point) (hb : b∈core n L) (eb : {f.center,b}∈twoCoreEdges n L G) :
        (supports n L b).card=3 ∧ ((a b=2 ∧ d b=2 ∧ m b=0) ∨ a b+d b=6) := by
      have eb' : {p,b}∈twoCoreEdges n L G := by simpa only [fc] using eb
      have typ := certificate_rigid_neighbor_classification n L hL hn tri hi ht triples
        P sub closed tight types p hp rigid.2.2 b hb eb'
      change (a b=2 ∧ d b=2 ∧ m b=0) ∨ ((supports n L b).card=3 ∧ a b+d b=6) at typ
      rcases typ with rigid|full
      · exact ⟨triples b hb,Or.inl rigid⟩
      · exact ⟨full.1,Or.inr full.2⟩
    exact UpperOpenMathNormalizedActualFull.certificate_normalized_neighbor_not_full
      n L hL hn tri hi ht f df neighbors q hq (by simpa only [fc] using edge) full
  have rclosed : SharedCoreClosed n L G R := by
    intro e he p hpe hp q hqe
    obtain ⟨hpP,hpRigid⟩ := mem_filter.mp hp
    have qp : q∈P := closed e he p hpe hpP hqe
    by_cases same : q=p
    · simpa only [same] using hp
    have used := (mem_filter.mp (mem_sdiff.mp he).1).1
    have pair : e={p,q} := by
      apply Eq.symm
      apply eq_of_subset_of_card_le
      · intro x hx
        rcases mem_insert.mp hx with rfl|hx
        · exact hpe
        · exact mem_singleton.mp hx ▸ hqe
      · rw [used_edge_card G used]
        simp only [card_pair (Ne.symm same)]
        norm_num
    have edge : {p,q}∈twoCoreEdges n L G := by simpa only [pair] using he
    have typ := certificate_rigid_neighbor_classification n L hL hn tri hi ht triples
      P sub closed tight types p hpP hpRigid.2.2 q (sub qp) edge
    change (a q=2 ∧ d q=2 ∧ m q=0) ∨ ((supports n L q).card=3 ∧ a q+d q=6) at typ
    rcases typ with rigid|full
    · exact mem_filter.mpr ⟨qp,rigid⟩
    · exact False.elim (noFull p hpP hpRigid q (sub qp) edge full.2)
  have empty : R=∅ := by
    by_contra h
    have nonempty : R.Nonempty := nonempty_iff_ne_empty.mpr h
    apply UpperOpenMathTwoTwoCore.certificate_closed_two_two_impossible
      n L hL hn tri hi ht R (fun p hp => sub (mem_filter.mp hp).1) nonempty rclosed
    intro p hp
    obtain ⟨hpP,ap,dp,mp⟩ := mem_filter.mp hp
    exact ⟨triples p (sub hpP),ap,dp⟩
  intro p hp rigid
  have mem : p∈R := mem_filter.mpr ⟨hp,rigid⟩
  rw [empty] at mem
  exact notMem_empty p mem

theorem closed_paid_zero_impossible {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (triples : ∀ p∈core n L, (supports n L p).card=3)
    (P : Finset Point) (sub : P⊆core n L) (nonempty : P.Nonempty)
    (closed : SharedCoreClosed n L (fun a => ofPredicate n L (tri a) hL (ht a)) P)
    (tight : TightOn n L hL hn tri ht P)
    (types : ∀ p∈P, ZeroType
      (ordinaryDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) p)
      (coreDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) p)
      (markedCount n L hL hn tri ht p)) : False :=
  UpperOpenMathPaidZeroEscape.closed_paid_zero_escape n L hL hn tri hi ht triples P sub nonempty closed tight types
    (closed_paid_zero_no_rigid n L hL hn tri hi ht triples P sub closed tight types)

#print axioms closed_paid_zero_no_rigid
#print axioms closed_paid_zero_impossible
end Kobon.UpperOpenMathPaidZeroRigidity
