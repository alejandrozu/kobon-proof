import Kobon.UpperOpenMathUnmarkedPoorResources
import Kobon.UpperOpenMathMarkedPaidOneWeights

/-! Actual extraction of the single-one-cap zero-cost classification. -/
namespace Kobon.UpperOpenMathOneCapActualData
open Cells FanGeometry UpperVertexBudget UpperTriangleIncidence UpperSharedIncidence
  UpperCoreExtraction UpperOpenMathCapHeavyTriples UpperOpenMathCoreComponents
  UpperOpenMathMarkedPorts UpperOpenMathUnmarkedPoorResources Finset
open scoped BigOperators
set_option maxHeartbeats 1000000

theorem certificate_single_one_cap_zero_data {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (triples : ∀ p∈core n L, (supports n L p).card=3)
    (P : Finset Point) (sub : P⊆core n L)
    (closed : SharedCoreClosed n L (fun a => ofPredicate n L (tri a) hL (ht a)) P)
    (degree : ∀ p∈P, coreDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) p≤5)
    (noA : ∀ p∈P, ¬(ordinaryDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) p=2 ∧
      coreDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) p=4 ∧ markedCount n L hL hn tri ht p=0))
    (oneB : (P.filter (fun p => ordinaryDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) p=1 ∧
      coreDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) p=5)).card=1)
    (c : Point) (hc : c∈P)
    (ac : ordinaryDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) c=1)
    (dc : coreDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) c=5)
    (reaches : ∀ b∈P.filter (fun p => ordinaryDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) p≤1 ∧
      ordinaryDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) p+
        coreDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) p≤2),
      {c,b}∈twoCoreEdges n L (fun a => ofPredicate n L (tri a) hL (ht a)))
    (zero : componentCost n L (fun a => ofPredicate n L (tri a) hL (ht a)) P=0) :
    let G := fun a => ofPredicate n L (tri a) hL (ht a)
    (∀ p∈P, markedCount n L hL hn tri ht p=0) ∧
      (P.filter (fun p => ordinaryDegree n L G p=1 ∧ coreDegree n L G p=3)).card=1 ∧
      ∀ p∈P, (ordinaryDegree n L G p=2 ∧ coreDegree n L G p=2) ∨
        (ordinaryDegree n L G p=1 ∧ coreDegree n L G p=5) ∨
        (ordinaryDegree n L G p=1 ∧ coreDegree n L G p=3) := by
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
  have strong := certificate_marked_capacity_reserved n L hL hn tri hi ht triples P sub closed c hc
    (by rw [ac]) (by rw [ac,dc]; omega) reaches
  change (∑ p∈P, m p)+(P.filter (fun p => a p≤1 ∧ a p+d p≤2)).card≤
    ∑ p∈P.filter (fun p => a p≤1 ∧ a p+d p≤2), d p at strong
  have identity := UpperOpenMathTripleCurvature.closed_curvature_identity n L G P closed localTriple
  have weightZero : (∑ p∈P, (6-2*(a p : ℤ)-d p))=0 := by
    rw [← identity]
    have zero' : componentCost n L G P=0 := zero
    rw [zero',mul_zero]
  have classification := UpperOpenMathMarkedPaidOneWeights.finite_paid_one_types P a d m ha had hfive degree
    hext hpartial hlow noA oneB strong weightZero
  exact classification.2

#print axioms certificate_single_one_cap_zero_data
end Kobon.UpperOpenMathOneCapActualData
