import Kobon.UpperOpenMathPaidZeroRigidity
import Kobon.UpperOpenMathMarkedPaidZeroWeights
import Kobon.UpperOpenMathMarkedCurvature

/-! Strict paid curvature halves the residual negative correction in each
actual shared-core component. There is no maximum-degree hypothesis. -/
namespace Kobon.UpperOpenMathPaidCurvatureBound
open Cells FanGeometry UpperFan UpperVertexBudget UpperTriangleIncidence UpperSharedIncidence
  UpperCoreExtraction UpperOpenMathCapHeavyTriples UpperOpenMathCoreComponents
  UpperOpenMathMarkedPorts UpperOpenMathMarkedCurvature UpperOpenMathMarkedCurvatureWeights
  UpperOpenMathPaidZeroTypes Finset
open scoped BigOperators
set_option maxHeartbeats 1000000

theorem certificate_closed_paid_data {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (triples : ∀ p∈core n L, (supports n L p).card=3)
    (P : Finset Point) (sub : P⊆core n L)
    (closed : SharedCoreClosed n L (fun a => ofPredicate n L (tri a) hL (ht a)) P) :
    let G := fun a => ofPredicate n L (tri a) hL (ht a)
    0≤2*componentCost n L G P+unpaidOn n L hL hn tri ht P ∧
      (2*componentCost n L G P+unpaidOn n L hL hn tri ht P=0 →
        TightOn n L hL hn tri ht P ∧
        ∀ p∈P, ZeroType (ordinaryDegree n L G p) (coreDegree n L G p) (markedCount n L hL hn tri ht p)) := by
  classical
  let G := fun a => ofPredicate n L (tri a) hL (ht a)
  let a := ordinaryDegree n L G
  let d := coreDegree n L G
  let m := markedCount n L hL hn tri ht
  have old := certificate_closed_marked_data n L hL hn tri hi ht triples P sub closed
  change 0≤2*componentCost n L G P+unpaidOn n L hL hn tri ht P ∧ _ at old
  change 0≤2*componentCost n L G P+unpaidOn n L hL hn tri ht P ∧ _
  refine ⟨old.1,?_⟩
  intro zero
  have localTriple (p : Point) (hp : p∈P) : (supports n L p).card=3 := triples p (sub hp)
  have ha (p : Point) (hp : p∈P) : a p≤3 := by
    have hh := UpperOpenMathActualFans.certificate_local_fan_bound n L hL hn tri hi ht p (sub hp)
    rw [localTriple p hp] at hh
    exact hh
  have had (p : Point) (hp : p∈P) : a p+d p≤6 := by
    have hh := UpperOpenMathMixedCapBudget.certificate_local_combined_degree n L hL hn tri hi ht p (sub hp)
    rw [localTriple p hp] at hh
    exact hh
  have hfive (p : Point) (hp : p∈P) : a p+d p≠5 :=
    UpperOpenMathTripleDegreeThree.certificate_triple_not_five n L hL hn tri hi ht p (sub hp) (localTriple p hp)
  have hext (p : Point) (hp : p∈P) (hpA : a p=3) : d p=3 ∧ m p=3 := by
    refine ⟨?_,marked_count_of_extremal_triple n L hL hn tri hi ht p (sub hp) (localTriple p hp) hpA⟩
    have he : 2*(supports n L p).card-3≤ordinaryDegree n L G p := by
      change 2*(supports n L p).card-3≤a p
      rw [localTriple p hp,hpA]
    exact UpperOpenMathSupportedCores.certificate_extremal_neighbor_count n L hL hn tri hi ht p (sub hp) he
  have hpartial (p : Point) (hp : p∈P) (hpA : a p=2) (hpD : d p=1) : 1≤m p := by
    have hm := marked_count_of_partial_triple n L hL hn tri hi ht p (sub hp) (localTriple p hp) hpA hpD
    change m p=1 at hm
    omega
  have hlow (p : Point) (hp : p∈P) (hpA : a p≤1) : m p=0 :=
    marked_count_zero_of_low n L hL hn tri hi ht triples p (sub hp) hpA
  have cap := closed_marked_port_budget n L hL hn tri hi ht triples P sub closed
  change (∑ p∈P, m p)≤∑ p∈P.filter (fun p => a p≤1 ∧ a p+d p≤2), d p at cap
  have identity := UpperOpenMathTripleCurvature.closed_curvature_identity n L G P closed localTriple
  have paid : (∑ p∈P, (6-2*(a p : ℤ)-d p+unpaidWeight (a p) (d p) (m p)))=
      2*componentCost n L G P+unpaidOn n L hL hn tri ht P := by
    rw [sum_add_distrib,← identity]
    rfl
  have finiteZero : (∑ p∈P, (6-2*(a p : ℤ)-d p+unpaidWeight (a p) (d p) (m p)))=0 := paid.trans zero
  exact UpperOpenMathMarkedPaidZeroWeights.finite_paid_zero_types P a d m ha had hfive hext hpartial hlow cap finiteZero

theorem certificate_closed_paid_positive {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (triples : ∀ p∈core n L, (supports n L p).card=3)
    (P : Finset Point) (sub : P⊆core n L) (nonempty : P.Nonempty)
    (closed : SharedCoreClosed n L (fun a => ofPredicate n L (tri a) hL (ht a)) P) :
    1≤2*componentCost n L (fun a => ofPredicate n L (tri a) hL (ht a)) P+unpaidOn n L hL hn tri ht P := by
  classical
  have data := certificate_closed_paid_data n L hL hn tri hi ht triples P sub closed
  dsimp only at data
  have nozero : 2*componentCost n L (fun a => ofPredicate n L (tri a) hL (ht a)) P+
      unpaidOn n L hL hn tri ht P≠0 := by
    intro hz
    obtain ⟨tight,types⟩ := data.2 hz
    exact UpperOpenMathPaidZeroRigidity.closed_paid_zero_impossible n L hL hn tri hi ht triples
      P sub nonempty closed tight types
  omega

noncomputable def halfPenaltyOn {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (ht : ∀ a, TrianglePredicate n L (tri a)) (P : Finset Point) : ℤ :=
  let G := fun a => ofPredicate n L (tri a) hL (ht a)
  ((P.filter (fun p => ordinaryDegree n L G p=2 ∧ coreDegree n L G p=4 ∧
    markedCount n L hL hn tri ht p=0)).card : ℤ)+
  ((((P.filter (fun p => ordinaryDegree n L G p=1 ∧ coreDegree n L G p=5)).card+1)/2 : ℕ) : ℤ)

theorem certificate_closed_half_penalty_bound {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (triples : ∀ p∈core n L, (supports n L p).card=3)
    (P : Finset Point) (sub : P⊆core n L) (nonempty : P.Nonempty)
    (closed : SharedCoreClosed n L (fun a => ofPredicate n L (tri a) hL (ht a)) P) :
    1≤componentCost n L (fun a => ofPredicate n L (tri a) hL (ht a)) P+halfPenaltyOn n L hL hn tri ht P := by
  classical
  let G := fun a => ofPredicate n L (tri a) hL (ht a)
  let A := (P.filter (fun p => ordinaryDegree n L G p=2 ∧ coreDegree n L G p=4 ∧
    markedCount n L hL hn tri ht p=0)).card
  let B := (P.filter (fun p => ordinaryDegree n L G p=1 ∧ coreDegree n L G p=5)).card
  have paid := certificate_closed_paid_positive n L hL hn tri hi ht triples P sub nonempty closed
  rw [unpaidOn_counts] at paid
  change 1≤2*componentCost n L G P+(2*(A : ℤ)+(B : ℤ)) at paid
  change 1≤componentCost n L G P+((A : ℤ)+(((B+1)/2 : ℕ) : ℤ))
  omega

theorem certificate_component_half_penalty_bound {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (triples : ∀ p∈core n L, (supports n L p).card=3) :
    let G := fun a => ofPredicate n L (tri a) hL (ht a)
    3*(Fintype.card α : ℤ)+(UpperEdgeInventory.edges n L\usedEdges G).card+coreComponentCount n L G≤
      (n : ℤ)*(n-2)+∑ s∈components n L G, halfPenaltyOn n L hL hn tri ht (componentVertices n L G s) := by
  classical
  let G := fun a => ofPredicate n L (tri a) hL (ht a)
  have each (s : (coreGraph n L G).ConnectedComponent) (hs : s∈components n L G) :
      (1 : ℤ)≤componentCost n L G (componentVertices n L G s)+
        halfPenaltyOn n L hL hn tri ht (componentVertices n L G s) :=
    certificate_closed_half_penalty_bound n L hL hn tri hi ht triples (componentVertices n L G s)
      (component_subset n L G s) (component_nonempty n L G s) (component_closed n L hL tri ht s)
  have summed := sum_le_sum each
  simp only [sum_add_distrib,sum_const,nsmul_eq_mul,mul_one,components_card] at summed
  have identity := certificate_component_cost_identity n L hL hn tri hi ht
  dsimp only at identity
  change 3*(Fintype.card α : ℤ)+(UpperEdgeInventory.edges n L\usedEdges G).card+coreComponentCount n L G≤
    (n : ℤ)*(n-2)+∑ s∈components n L G, halfPenaltyOn n L hL hn tri ht (componentVertices n L G s)
  linarith

#print axioms certificate_closed_paid_positive
#print axioms certificate_closed_half_penalty_bound
#print axioms certificate_component_half_penalty_bound

theorem component_half_penalty_sum {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (ht : ∀ a, TrianglePredicate n L (tri a)) :
    let G := fun a => ofPredicate n L (tri a) hL (ht a)
    (∑ s∈components n L G, halfPenaltyOn n L hL hn tri ht (componentVertices n L G s))=
      ((core n L).filter (fun p => ordinaryDegree n L G p=2 ∧ coreDegree n L G p=4 ∧
        markedCount n L hL hn tri ht p=0)).card+
      ∑ s∈components n L G,
        ((((componentVertices n L G s).filter (fun p => ordinaryDegree n L G p=1 ∧
          coreDegree n L G p=5)).card+1)/2 : ℕ) := by
  classical
  let G := fun a => ofPredicate n L (tri a) hL (ht a)
  let pred := fun p => ordinaryDegree n L G p=2 ∧ coreDegree n L G p=4 ∧ markedCount n L hL hn tri ht p=0
  have counts : (∑ s∈components n L G, (((componentVertices n L G s).filter pred).card : ℤ))=
      (((core n L).filter pred).card : ℤ) := by
    have h := component_sum n L G (fun p => if pred p then (1 : ℤ) else 0)
    have indicatorCount (Q : Finset Point) :
        (∑ p∈Q, if pred p then (1 : ℤ) else 0)=((Q.filter pred).card : ℤ) :=
      Finset.sum_boole pred Q
    have lhs := sum_congr rfl (fun s (_ : s∈components n L G) => indicatorCount (componentVertices n L G s))
    rw [lhs,indicatorCount (core n L)] at h
    exact h
  unfold halfPenaltyOn
  dsimp only
  rw [sum_add_distrib,counts]
  simp only [Nat.cast_sum]
  rfl

theorem certificate_half_exception_bound {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (triples : ∀ p∈core n L, (supports n L p).card=3) :
    let G := fun a => ofPredicate n L (tri a) hL (ht a)
    3*(Fintype.card α : ℤ)+(UpperEdgeInventory.edges n L\usedEdges G).card+coreComponentCount n L G≤
      (n : ℤ)*(n-2)+
      ((core n L).filter (fun p => ordinaryDegree n L G p=2 ∧ coreDegree n L G p=4 ∧
        markedCount n L hL hn tri ht p=0)).card+
      ∑ s∈components n L G,
        ((((componentVertices n L G s).filter (fun p => ordinaryDegree n L G p=1 ∧
          coreDegree n L G p=5)).card+1)/2 : ℕ) := by
  have h := certificate_component_half_penalty_bound n L hL hn tri hi ht triples
  dsimp only at h ⊢
  have formula := component_half_penalty_sum n L hL hn tri ht
  dsimp only at formula
  rw [formula] at h
  linarith

#print axioms certificate_half_exception_bound
end Kobon.UpperOpenMathPaidCurvatureBound
