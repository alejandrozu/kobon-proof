import Kobon.UpperOpenMathMarkedZeroGeometry
import Kobon.UpperOpenMathFullTripleChart

/-! The six actual local types possible at zero paid curvature. -/
namespace Kobon.UpperOpenMathPaidZeroTypes
open Cells FanGeometry UpperFan UpperVertexBudget UpperTriangleIncidence UpperSharedIncidence
  UpperCoreExtraction UpperOpenMathCapHeavyTriples UpperOpenMathCoreComponents
  UpperOpenMathMarkedPorts UpperOpenMathMarkedZeroGeometry Finset
open scoped BigOperators

def ZeroType (a d m : ℕ) : Prop :=
  (a=2 ∧ d=2 ∧ m=0) ∨ (a=2 ∧ d=4 ∧ m=1) ∨
  (a=0 ∧ d=2 ∧ m=0) ∨ (a=0 ∧ d=6 ∧ m=0) ∨
  (a=2 ∧ d=4 ∧ m=0) ∨ (a=1 ∧ d=5 ∧ m=0)

def TightOn {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (ht : ∀ a, TrianglePredicate n L (tri a)) (P : Finset Point) : Prop :=
  let G := fun a => ofPredicate n L (tri a) hL (ht a)
  (∑ p∈P, markedCount n L hL hn tri ht p)=
    ∑ p∈P.filter (fun p => ordinaryDegree n L G p≤1 ∧
      ordinaryDegree n L G p+coreDegree n L G p≤2), coreDegree n L G p

theorem marked_positive_type (a d m : ℕ) (type : ZeroType a d m) (hm : 0<m) :
    a=2 ∧ d=4 ∧ m=1 := by
  rcases type with r|h|b|f|v|o <;> omega

theorem no_marked_edge_of_zero {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (ht : ∀ a, TrianglePredicate n L (tri a)) (p : Point)
    (zero : markedCount n L hL hn tri ht p=0) (e : Edge) :
    e∉markedEdges n L hL hn tri ht p := by
  intro he
  have positive : 0<markedCount n L hL hn tri ht p := card_pos.mpr ⟨e,he⟩
  omega

theorem certificate_rigid_neighbor_classification {α : Type*} [Fintype α]
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
      (markedCount n L hL hn tri ht p))
    (p : Point) (hp : p∈P) (zero : markedCount n L hL hn tri ht p=0)
    (q : Point) (hq : q∈core n L)
    (edge : {p,q}∈twoCoreEdges n L (fun a => ofPredicate n L (tri a) hL (ht a))) :
    let G := fun a => ofPredicate n L (tri a) hL (ht a)
    (ordinaryDegree n L G q=2 ∧ coreDegree n L G q=2 ∧ markedCount n L hL hn tri ht q=0) ∨
      ((supports n L q).card=3 ∧ ordinaryDegree n L G q+coreDegree n L G q=6) := by
  classical
  let G := fun a => ofPredicate n L (tri a) hL (ht a)
  have qp : q∈P := closed {p,q} edge p (by simp) hp (by simp)
  have localType : ZeroType (ordinaryDegree n L G q) (coreDegree n L G q)
      (markedCount n L hL hn tri ht q) := types q qp
  change (ordinaryDegree n L G q=2 ∧ coreDegree n L G q=2 ∧ markedCount n L hL hn tri ht q=0) ∨
    ((supports n L q).card=3 ∧ ordinaryDegree n L G q+coreDegree n L G q=6)
  rcases localType with r|h|b|f|v|o
  · exact Or.inl r
  · exact Or.inr ⟨triples q hq,by omega⟩
  · have poor : ordinaryDegree n L G q≤1 ∧ ordinaryDegree n L G q+coreDegree n L G q≤2 := by omega
    exact False.elim (unmarked_target_not_poor n L hL hn tri hi ht triples P sub closed tight
      p q qp poor edge (no_marked_edge_of_zero n L hL hn tri ht p zero {p,q}))
  · exact Or.inr ⟨triples q hq,by omega⟩
  · exact Or.inr ⟨triples q hq,by omega⟩
  · exact Or.inr ⟨triples q hq,by omega⟩

#print axioms certificate_rigid_neighbor_classification
end Kobon.UpperOpenMathPaidZeroTypes
