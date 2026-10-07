import Kobon.UpperOpenMathMarkedPorts
import Kobon.UpperOpenMathMarkedCurvatureWeights

/-! Actual marked-ray curvature and its equality case, with every local
weight and the marked capacity extracted from a line arrangement. -/
namespace Kobon.UpperOpenMathMarkedCurvature
open Cells FanGeometry UpperVertexBudget UpperTriangleIncidence UpperSharedIncidence
  UpperCoreExtraction UpperOpenMathCapHeavyTriples UpperOpenMathCoreComponents UpperOpenMathTripleCurvature
  UpperOpenMathMarkedPorts UpperOpenMathMarkedCurvatureWeights Finset
open scoped BigOperators
set_option maxHeartbeats 1000000

noncomputable def unpaidOn {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (ht : ∀ a, TrianglePredicate n L (tri a)) (P : Finset Point) : ℤ :=
  let G := fun a => ofPredicate n L (tri a) hL (ht a)
  ∑ p∈P, unpaidWeight (ordinaryDegree n L G p) (coreDegree n L G p)
    (markedCount n L hL hn tri ht p)

theorem unpaidOn_nonnegative {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (ht : ∀ a, TrianglePredicate n L (tri a)) (P : Finset Point) :
    0≤unpaidOn n L hL hn tri ht P :=
  sum_nonneg (fun p _ => unpaidWeight_nonnegative _ _ _)

theorem certificate_closed_marked_data {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (triples : ∀ p∈core n L, (supports n L p).card=3)
    (P : Finset Point) (sub : P⊆core n L)
    (closed : SharedCoreClosed n L (fun a => ofPredicate n L (tri a) hL (ht a)) P) :
    let G := fun a => ofPredicate n L (tri a) hL (ht a)
    let m := markedCount n L hL hn tri ht
    0≤2*componentCost n L G P+unpaidOn n L hL hn tri ht P ∧
    (unpaidOn n L hL hn tri ht P=0 → componentCost n L G P=0 →
      (∑ p∈P, m p)=∑ p∈P.filter (fun p => ordinaryDegree n L G p≤1 ∧
        ordinaryDegree n L G p+coreDegree n L G p≤2), coreDegree n L G p ∧
      ∀ p∈P,
        (ordinaryDegree n L G p=2 ∧ coreDegree n L G p=2 ∧ m p=0) ∨
        (ordinaryDegree n L G p=2 ∧ coreDegree n L G p=4 ∧ m p=1) ∨
        (ordinaryDegree n L G p=0 ∧ coreDegree n L G p=2 ∧ m p=0) ∨
        (ordinaryDegree n L G p=0 ∧ coreDegree n L G p=6 ∧ m p=0)) := by
  classical
  let G := fun a => ofPredicate n L (tri a) hL (ht a)
  let a := ordinaryDegree n L G
  let d := coreDegree n L G
  let m := markedCount n L hL hn tri ht
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
  have discharge := finite_marked_curvature P a d m ha had hfive hext hpartial hlow cap
  have identity := closed_curvature_identity n L G P closed localTriple
  have paid : (∑ p∈P, (6-2*(a p : ℤ)-d p+unpaidWeight (a p) (d p) (m p)))=
      2*componentCost n L G P+unpaidOn n L hL hn tri ht P := by
    rw [sum_add_distrib,← identity]
    rfl
  change 0≤2*componentCost n L G P+unpaidOn n L hL hn tri ht P ∧ _
  refine ⟨?_,?_⟩
  · rw [← paid]
    have positiveE : 0≤3*((P.filter (fun p => a p=3)).card : ℤ) := by positivity
    have positiveA : 0≤3*((P.filter (fun p => a p=2 ∧ d p=1)).card : ℤ) := by positivity
    linarith
  · intro unpaidZero costZero
    have eachUnpaid : ∀ p∈P, unpaidWeight (a p) (d p) (m p)=0 :=
      (sum_eq_zero_iff_of_nonneg (fun p _ => unpaidWeight_nonnegative (a p) (d p) (m p))).mp unpaidZero
    have zero : (∑ p∈P, (6-2*(a p : ℤ)-d p))=0 := by rw [← identity,costZero]; ring
    exact finite_marked_zero_types P a d m ha had hfive hext hpartial hlow cap eachUnpaid zero

theorem unpaidOn_counts {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (ht : ∀ a, TrianglePredicate n L (tri a)) (P : Finset Point) :
    let G := fun a => ofPredicate n L (tri a) hL (ht a)
    unpaidOn n L hL hn tri ht P=
      2*((P.filter (fun p => ordinaryDegree n L G p=2 ∧ coreDegree n L G p=4 ∧
        markedCount n L hL hn tri ht p=0)).card : ℤ)+
      ((P.filter (fun p => ordinaryDegree n L G p=1 ∧ coreDegree n L G p=5)).card : ℤ) := by
  classical
  have he (a d m : ℕ) : unpaidWeight a d m=
      2*(if a=2 ∧ d=4 ∧ m=0 then (1 : ℤ) else 0)+(if a=1 ∧ d=5 then 1 else 0) := by
    unfold unpaidWeight
    split_ifs <;> omega
  unfold unpaidOn
  simp_rw [he]
  simp only [sum_add_distrib,← mul_sum,sum_ite,sum_const_zero,add_zero,
    sum_const,nsmul_eq_mul,mul_one]

#print axioms certificate_closed_marked_data
#print axioms unpaidOn_counts
end Kobon.UpperOpenMathMarkedCurvature
