import Kobon.UpperOpenMathAntipodalStarWeights
import Kobon.UpperOpenMathMixedCurvatureBound

/-! Actual adjusted local weights next to a full two-cap triple core. -/
namespace Kobon.UpperOpenMathMixedStarWeights
open Cells FanGeometry UpperFan UpperVertexBudget UpperTriangleIncidence UpperSharedIncidence
  UpperCoreExtraction UpperOpenMathCapHeavyTriples UpperOpenMathCoreComponents
  UpperOpenMathActualFans UpperOpenMathMixedDegreeThree Finset
open scoped BigOperators
set_option maxHeartbeats 1000000

noncomputable def mixedWeight {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (G : α → TriangleGeometry) (p : Point) : ℤ :=
  let r := (supports n L p).card
  if 4≤r then 4*(r : ℤ)-2*ordinaryDegree n L G p-coreDegree n L G p else
    2*(r : ℤ)*(r-2)-2*ordinaryDegree n L G p-coreDegree n L G p

theorem mixed_weight_sum {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (G : α → TriangleGeometry)
    (P : Finset Point) (closed : SharedCoreClosed n L G P) :
    (∑ p∈P, mixedWeight n L G p)=2*(componentCost n L G P-higherSurplusOn n L P) := by
  classical
  let r := fun p => (supports n L p).card
  let a := ordinaryDegree n L G
  let d := coreDegree n L G
  have dsum : (∑ p∈P, (d p : ℤ))=2*((componentEdges n L G P).card : ℤ) := by
    exact_mod_cast closed_degree_sum n L G P closed
  have each (p : Point) : mixedWeight n L G p=
      2*(r p : ℤ)*(r p-2)-2*a p-d p-
      (if 4≤r p then 2*(r p : ℤ)*(r p-4) else 0) := by
    dsimp [mixedWeight]
    split_ifs <;> ring
  have sumHigher : (∑ p∈P, if 4≤r p then 2*(r p : ℤ)*(r p-4) else 0)=2*higherSurplusOn n L P := by
    rw [← sum_filter]
    change (∑ p∈P.filter (fun p => 4≤r p), 2*(r p : ℤ)*(r p-4))=
      2*(∑ p∈P.filter (fun p => 4≤r p), (r p : ℤ)*(r p-4))
    rw [mul_sum]
    exact sum_congr rfl (fun p _ => by ring)
  have sumLoss : (∑ p∈P, 2*(r p : ℤ)*(r p-2))=2*(∑ p∈P, (r p : ℤ)*(r p-2)) := by
    rw [mul_sum]
    exact sum_congr rfl (fun p _ => by ring)
  change (∑ p∈P, mixedWeight n L G p)=2*((∑ p∈P, (r p : ℤ)*(r p-2))-
    (∑ p∈P, (a p : ℤ))-(componentEdges n L G P).card-higherSurplusOn n L P)
  rw [sum_congr rfl (fun p _ => each p)]
  simp only [sum_sub_distrib]
  rw [sumLoss,← mul_sum,dsum,sumHigher]
  ring

theorem certificate_weight_neighbor_full_two_cap {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (p c : Point) (hp : p∈core n L) (hc : c∈core n L)
    (rc : (supports n L c).card=3)
    (ac : ordinaryDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) c=2)
    (dc : coreDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) c=4)
    (edge : {p,c}∈twoCoreEdges n L (fun a => ofPredicate n L (tri a) hL (ht a)))
    (degree : coreDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) p≤3) :
    let G := fun a => ofPredicate n L (tri a) hL (ht a)
    0≤mixedWeight n L G p ∧
      (coreDegree n L G p≤1 → 3≤mixedWeight n L G p) ∧
      (coreDegree n L G p≤2 →
        (mixedWeight n L G p=0 ∨ 2≤mixedWeight n L G p) ∧
        (mixedWeight n L G p=0 → (supports n L p).card=3 ∧ ordinaryDegree n L G p=2 ∧ coreDegree n L G p=2) ∧
        (4≤(supports n L p).card → 6≤mixedWeight n L G p)) := by
  classical
  let G := fun a => ofPredicate n L (tri a) hL (ht a)
  let r := (supports n L p).card
  let a := ordinaryDegree n L G p
  let d := coreDegree n L G p
  have hr : 3≤r := core_multiplicity n L hL hp
  have ha : a≤2*r-3 := certificate_local_fan_bound n L hL hn tri hi ht p hp
  have hd : d≤3 := degree
  have positive : 1≤d := by
    apply one_le_card.mpr
    exact ⟨{p,c},mem_filter.mpr ⟨edge,by simp⟩⟩
  by_cases high : 4≤r
  · have weight : mixedWeight n L G p=4*(r : ℤ)-2*a-d := by
      change (if 4≤r then 4*(r : ℤ)-2*a-d else 2*(r : ℤ)*(r-2)-2*a-d)=_
      rw [if_pos high]
    change 0≤mixedWeight n L G p ∧
      (d≤1 → 3≤mixedWeight n L G p) ∧
      (d≤2 → ((mixedWeight n L G p=0 ∨ 2≤mixedWeight n L G p) ∧
        (mixedWeight n L G p=0 → r=3 ∧ a=2 ∧ d=2) ∧
        (4≤r → 6≤mixedWeight n L G p)))
    simp only [weight]
    change 0≤4*(r : ℤ)-2*a-d ∧
      (d≤1 → 3≤4*(r : ℤ)-2*a-d) ∧
      (d≤2 → ((4*(r : ℤ)-2*a-d=0 ∨ 2≤4*(r : ℤ)-2*a-d) ∧
        (4*(r : ℤ)-2*a-d=0 → r=3 ∧ a=2 ∧ d=2) ∧
        (4≤r → 6≤4*(r : ℤ)-2*a-d)))
    have lower : 3≤4*(r : ℤ)-2*a-d := by omega
    refine ⟨by omega,(fun _ => lower),?_⟩
    intro h2
    have small := UpperOpenMathDegreeBudgets.certificate_local_degree_two n L hL hn tri hi ht p hp h2
    change a≤2*r-4 at small
    omega
  · have rp : r=3 := by omega
    have rpoint : (supports n L p).card=3 := rp
    have noHeavy : ¬(a=3 ∨ (a=2 ∧ d=1)) := by
      intro heavy
      have poor := UpperOpenMathMarkedPoverty.certificate_cap_heavy_neighbor_sum
        n L hL hn tri hi ht p c hp hc rpoint rc heavy edge
      change ordinaryDegree n L G c≤1 ∧ ordinaryDegree n L G c+coreDegree n L G c≤2 at poor
      rw [ac,dc] at poor
      omega
    have noFive := UpperOpenMathTripleDegreeThree.certificate_triple_not_five n L hL hn tri hi ht p hp rpoint
    change a+d≠5 at noFive
    change 0≤mixedWeight n L G p ∧ _
    have weight : mixedWeight n L G p=6-2*(a : ℤ)-d := by
      simp only [mixedWeight,rpoint,show ¬(4≤3) by omega,if_false]
      ring
    rw [weight]
    change 0≤6-2*(a : ℤ)-d ∧
      (d≤1 → 3≤6-2*(a : ℤ)-d) ∧
      (d≤2 → ((6-2*(a : ℤ)-d=0 ∨ 2≤6-2*(a : ℤ)-d) ∧
        (6-2*(a : ℤ)-d=0 → r=3 ∧ a=2 ∧ d=2) ∧
        (4≤r → 6≤6-2*(a : ℤ)-d)))
    omega

#print axioms mixed_weight_sum
#print axioms certificate_weight_neighbor_full_two_cap
end Kobon.UpperOpenMathMixedStarWeights
