import Kobon.UpperOpenMathMixedDegreeFour
import Kobon.UpperOpenMathMixedCurvatureWeights
import Kobon.UpperOpenMathClosedTripleFull

/-!
# Degree-free mixed-multiplicity component curvature

Every actual nonempty shared-core component contributes one defect unit,
plus `r*(r-4)` at each vertex of multiplicity at least four, with explicit corrections for full two-cap and one-cap triple cores.
No core-degree restriction is imposed. Equality is excluded by actual full
sharing and by the balanced-pair/full-third geometric obstruction.
-/
namespace Kobon.UpperOpenMathMixedCurvature
open Cells FanGeometry UpperVertexBudget UpperTriangleIncidence UpperSharedIncidence
  UpperCoreExtraction UpperOpenMathCapHeavyTriples UpperOpenMathCoreComponents
  UpperOpenMathActualFans Finset
open scoped BigOperators

open UpperOpenMathMixedDegreeThree

open UpperOpenMathMixedDegreeFour

noncomputable def oneCapFullOn {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (G : α → TriangleGeometry) (P : Finset Point) : ℕ := by
  classical
  exact (P.filter (fun p => (supports n L p).card=3 ∧
    ordinaryDegree n L G p=1 ∧ coreDegree n L G p=5)).card

noncomputable def oneCapFullCount {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (G : α → TriangleGeometry) : ℕ :=
  oneCapFullOn n L G (core n L)

noncomputable def componentOneCapHalf {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (G : α → TriangleGeometry) : ℕ :=
  ∑ s∈components n L G, (oneCapFullOn n L G (componentVertices n L G s)+1)/2

theorem certificate_closed_mixed_paid_positive {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (P : Finset Point) (sub : P⊆core n L) (nonempty : P.Nonempty)
    (closed : SharedCoreClosed n L (fun a => ofPredicate n L (tri a) hL (ht a)) P)
    :
    let G := fun a => ofPredicate n L (tri a) hL (ht a)
    1≤2*(componentCost n L G P-higherSurplusOn n L P)+
      2*twoCapFullOn n L G P+oneCapFullOn n L G P := by
  classical
  let G := fun a => ofPredicate n L (tri a) hL (ht a)
  let r := fun p => (supports n L p).card
  let a := ordinaryDegree n L G
  let d := coreDegree n L G
  let E := P.filter (fun p => r p=3 ∧ a p=3)
  let B := P.filter (fun p => r p=3 ∧ a p≤1 ∧ a p+d p≤2)
  let H := P.filter (fun p => 4≤r p)
  let W := fun p => if 4≤r p then 4*(r p : ℤ)-2*a p-d p else
    2*(r p : ℤ)*(r p-2)-2*a p-d p
  have hr (p : Point) (hp : p∈P) : 3≤r p := core_multiplicity n L hL (sub hp)
  have ha (p : Point) (hp : p∈P) : a p≤2*r p-3 :=
    certificate_local_fan_bound n L hL hn tri hi ht p (sub hp)
  have had (p : Point) (hp : p∈P) : a p+d p≤2*r p :=
    UpperOpenMathMixedCapBudget.certificate_local_combined_degree n L hL hn tri hi ht p (sub hp)
  have hfive (p : Point) (hp : p∈P) (hpR : r p=3) : a p+d p≠5 :=
    UpperOpenMathTripleDegreeThree.certificate_triple_not_five n L hL hn tri hi ht p (sub hp) hpR
  have hext (p : Point) (hp : p∈P) (hpR : r p=3) (hpA : a p=3) : d p=3 := by
    have hx : 2*(supports n L p).card-3≤ordinaryDegree n L G p := by
      change 2*r p-3≤a p
      rw [hpR,hpA]
    exact UpperOpenMathSupportedCores.certificate_extremal_neighbor_count n L hL hn tri hi ht p (sub hp) hx
  have counts := UpperOpenMathMixedDegreeThreeResources.closed_mixed_extremal_counts n L hL hn tri hi ht P sub closed
  change (∑ p∈E, d p)=3*E.card ∧ 3*E.card≤(∑ p∈B, d p)+(∑ p∈H, d p) at counts
  have discharge := UpperOpenMathMixedCurvatureWeights.finite_mixed_paid_weight_rigidity
    P r a d hr ha had hfive hext counts.2
  have dsum : (∑ p∈P, (d p : ℤ))=2*((componentEdges n L G P).card : ℤ) := by
    exact_mod_cast closed_degree_sum n L G P closed
  have each (p : Point) : W p=
      2*(r p : ℤ)*(r p-2)-2*a p-d p-
      (if 4≤r p then 2*(r p : ℤ)*(r p-4) else 0) := by
    dsimp [W]
    split_ifs <;> ring
  have sumHigher : (∑ p∈P, if 4≤r p then 2*(r p : ℤ)*(r p-4) else 0)=2*higherSurplusOn n L P := by
    rw [← sum_filter]
    change (∑ p∈P.filter (fun p => 4≤r p), 2*(r p : ℤ)*(r p-4))=
      2*(∑ p∈P.filter (fun p => 4≤r p), (r p : ℤ)*(r p-4))
    rw [mul_sum]
    apply sum_congr rfl
    intro p hp
    ring
  have sumLoss : (∑ p∈P, 2*(r p : ℤ)*(r p-2))=2*(∑ p∈P, (r p : ℤ)*(r p-2)) := by
    rw [mul_sum]
    exact sum_congr rfl (fun p _ => by ring)
  have identity : (∑ p∈P, W p)+2*twoCapFullOn n L G P+oneCapFullOn n L G P=2*(componentCost n L G P-higherSurplusOn n L P)+2*twoCapFullOn n L G P+oneCapFullOn n L G P := by
    change (∑ p∈P, W p)+2*twoCapFullOn n L G P+oneCapFullOn n L G P=2*((∑ p∈P, (r p : ℤ)*(r p-2))-
      (∑ p∈P, (a p : ℤ))-(componentEdges n L G P).card-higherSurplusOn n L P)+2*twoCapFullOn n L G P+oneCapFullOn n L G P
    rw [sum_congr rfl (fun p _ => each p)]
    simp only [sum_sub_distrib]
    rw [sumLoss,← mul_sum,dsum,sumHigher]
    ring
  have nonneg : 0≤2*(componentCost n L G P-higherSurplusOn n L P)+2*twoCapFullOn n L G P+oneCapFullOn n L G P := by
    have hh := discharge.1
    change 0≤(∑ p∈P, W p)+2*twoCapFullOn n L G P+oneCapFullOn n L G P at hh
    rw [identity] at hh
    omega
  have nozero : 2*(componentCost n L G P-higherSurplusOn n L P)+2*twoCapFullOn n L G P+oneCapFullOn n L G P≠0 := by
    intro hz
    have wzero : (∑ p∈P, W p)+2*twoCapFullOn n L G P+oneCapFullOn n L G P=0 := by rw [identity,hz]
    obtain ⟨bempty,hsum,high,low⟩ := discharge.2 wzero
    change B=∅ at bempty
    change (∑ p∈H, d p)=3*E.card at hsum
    have inject := UpperOpenMathMixedDegreeThreeResources.closed_mixed_extremal_edge_injection
      n L hL hn tri hi ht P sub closed
    change ∀ e∈twoCoreEdges n L G, (e∩E).card≤(e∩(B∪H)).card at inject
    simp only [bempty,empty_union] at inject
    have equalSum : (∑ e∈twoCoreEdges n L G, (e∩E).card)=
        ∑ e∈twoCoreEdges n L G, (e∩H).card := by
      rw [← UpperOpenMathCoreDoubleCount.endpoint_double_count,
        ← UpperOpenMathCoreDoubleCount.endpoint_double_count]
      exact counts.1.trans hsum.symm
    have equal := (sum_eq_sum_iff_of_le inject).mp equalSum
    have ehDisjoint : Disjoint E H := by
      apply disjoint_left.mpr
      intro p hpE hpH
      have hp3 := (mem_filter.mp hpE).2.1
      have hp4 := (mem_filter.mp hpH).2
      omega
    let X := E∪H
    have xClosed : SharedCoreClosed n L G X :=
      UpperOpenMathClosedExtremal.union_closed_of_equal_endpoint_counts n L G E H ehDisjoint equal
    have xSub : X⊆core n L := by
      exact (union_subset (filter_subset _ _) (filter_subset _ _)).trans sub
    have full (p : Point) (hp : p∈X) : a p+d p=2*r p := by
      rcases mem_union.mp hp with hpE|hpH
      · obtain ⟨hpP,hpR,hpA⟩ := mem_filter.mp hpE
        have hpD := hext p hpP hpR hpA
        rw [hpR,hpA,hpD]
      · obtain ⟨hpP,hpR⟩ := mem_filter.mp hpH
        exact high p hpP hpR
    by_cases xNonempty : X.Nonempty
    · exact UpperOpenMathClosedFullSharing.certificate_closed_full_sharing_impossible
        n L hL hn tri hi ht X xSub xNonempty xClosed full
    · have xEmpty : X=∅ := not_nonempty_iff_eq_empty.mp xNonempty
      have eEmpty : E=∅ := (union_eq_empty.mp xEmpty).1
      have hEmpty : H=∅ := (union_eq_empty.mp xEmpty).2
      have rigid (p : Point) (hp : p∈P) : r p=3 ∧ ((a p=2 ∧ d p=2) ∨ a p+d p=6) := by
        have hpR : r p=3 := by
          have hp3 := hr p hp
          have hp4 : ¬4≤r p := by
            intro h
            have hm : p∈H := mem_filter.mpr ⟨hp,h⟩
            rw [hEmpty] at hm
            exact notMem_empty p hm
          omega
        have hpA : a p≠3 := by
          intro h
          have hm : p∈E := mem_filter.mpr ⟨hp,hpR,h⟩
          rw [eEmpty] at hm
          exact notMem_empty p hm
        have kinds := low p hp hpR hpA
        refine ⟨hpR,?_⟩
        rcases kinds with ⟨ha2,hd2|hd4⟩|⟨ha1,hd5⟩|⟨ha0,hd6⟩
        · exact Or.inl ⟨ha2,hd2⟩
        · exact Or.inr (by omega)
        · exact Or.inr (by omega)
        · exact Or.inr (by omega)
      exact UpperOpenMathClosedTripleFull.certificate_closed_triple_two_or_full_impossible
        n L hL hn tri hi ht P sub nonempty closed
          (fun p hp => (rigid p hp).1) (fun p hp => (rigid p hp).2)
  change 1≤2*(componentCost n L G P-higherSurplusOn n L P)+2*twoCapFullOn n L G P+oneCapFullOn n L G P
  omega

#print axioms certificate_closed_mixed_paid_positive
end Kobon.UpperOpenMathMixedCurvature
