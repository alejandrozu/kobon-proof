import Kobon.UpperOpenMathMixedDegreeThree
import Kobon.UpperOpenMathMixedDegreeFourWeights
import Kobon.UpperOpenMathTwoCapNeighborRigidity

/-!
# Mixed multiplicities with at most four shared core neighbors

Every actual nonempty shared-core component contributes one defect unit,
plus `r*(r-4)` at each vertex of multiplicity at least four, with a unit
correction for each full two-cap triple core. Equality is excluded by full
sharing and by the balanced-pair/full-third geometric obstruction.
-/
namespace Kobon.UpperOpenMathMixedDegreeFour
open Cells FanGeometry UpperVertexBudget UpperTriangleIncidence UpperSharedIncidence
  UpperCoreExtraction UpperOpenMathCapHeavyTriples UpperOpenMathCoreComponents
  UpperOpenMathActualFans Finset
open scoped BigOperators

open UpperOpenMathMixedDegreeThree

noncomputable def twoCapFullOn {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (G : α → TriangleGeometry) (P : Finset Point) : ℕ := by
  classical
  exact (P.filter (fun p => (supports n L p).card=3 ∧
    ordinaryDegree n L G p=2 ∧ coreDegree n L G p=4)).card

noncomputable def twoCapFullCount {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (G : α → TriangleGeometry) : ℕ :=
  twoCapFullOn n L G (core n L)

theorem certificate_closed_mixed_degree_four_cost {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (P : Finset Point) (sub : P⊆core n L) (nonempty : P.Nonempty)
    (closed : SharedCoreClosed n L (fun a => ofPredicate n L (tri a) hL (ht a)) P)
    (degree : ∀ p∈P, coreDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) p≤4) :
    1+higherSurplusOn n L P≤(twoCapFullOn n L (fun a => ofPredicate n L (tri a) hL (ht a)) P : ℤ)+componentCost n L (fun a => ofPredicate n L (tri a) hL (ht a)) P := by
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
  have hd : ∀ p∈P, d p≤4 := degree
  have hfive (p : Point) (hp : p∈P) (hpR : r p=3) : a p+d p≠5 :=
    UpperOpenMathTripleDegreeThree.certificate_triple_not_five n L hL hn tri hi ht p (sub hp) hpR
  have hext (p : Point) (hp : p∈P) (hpR : r p=3) (hpA : a p=3) : d p=3 := by
    have hx : 2*(supports n L p).card-3≤ordinaryDegree n L G p := by
      change 2*r p-3≤a p
      rw [hpR,hpA]
    exact UpperOpenMathSupportedCores.certificate_extremal_neighbor_count n L hL hn tri hi ht p (sub hp) hx
  have counts := UpperOpenMathMixedDegreeThreeResources.closed_mixed_extremal_counts n L hL hn tri hi ht P sub closed
  change (∑ p∈E, d p)=3*E.card ∧ 3*E.card≤(∑ p∈B, d p)+(∑ p∈H, d p) at counts
  have discharge := UpperOpenMathMixedDegreeFourWeights.finite_mixed_four_weight_rigidity
    P r a d hr ha had hd hfive hext counts.2
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
  have identity : (∑ p∈P, W p)+2*twoCapFullOn n L G P=2*(componentCost n L G P+(twoCapFullOn n L G P : ℤ)-higherSurplusOn n L P) := by
    change (∑ p∈P, W p)+2*twoCapFullOn n L G P=2*((∑ p∈P, (r p : ℤ)*(r p-2))-
      (∑ p∈P, (a p : ℤ))-(componentEdges n L G P).card+(twoCapFullOn n L G P : ℤ)-higherSurplusOn n L P)
    rw [sum_congr rfl (fun p _ => each p)]
    simp only [sum_sub_distrib]
    rw [sumLoss,← mul_sum,dsum,sumHigher]
    ring
  have nonneg : 0≤componentCost n L G P+(twoCapFullOn n L G P : ℤ)-higherSurplusOn n L P := by
    have hh := discharge.1
    change 0≤(∑ p∈P, W p)+2*twoCapFullOn n L G P at hh
    rw [identity] at hh
    omega
  have nozero : componentCost n L G P+(twoCapFullOn n L G P : ℤ)-higherSurplusOn n L P≠0 := by
    intro hz
    have wzero : (∑ p∈P, W p)+2*twoCapFullOn n L G P=0 := by rw [identity,hz]; ring
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
      have rigid (p : Point) (hp : p∈P) : r p=3 ∧ a p=2 ∧ (d p=2 ∨ d p=4) := by
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
        exact ⟨hpR,low p hp hpR hpA⟩
      exact UpperOpenMathTwoCapNeighborRigidity.certificate_closed_two_or_four_impossible
        n L hL hn tri hi ht P sub nonempty closed rigid
  change 1+higherSurplusOn n L P≤(twoCapFullOn n L G P : ℤ)+componentCost n L G P
  omega

theorem component_two_cap_full_sum {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (G : α → TriangleGeometry) :
    (∑ s∈components n L G, twoCapFullOn n L G (componentVertices n L G s))=twoCapFullCount n L G := by
  classical
  have as_sum (Q : Finset Point) : (twoCapFullOn n L G Q : ℤ)=
      ∑ p∈Q, if (supports n L p).card=3 ∧ ordinaryDegree n L G p=2 ∧ coreDegree n L G p=4
        then (1 : ℤ) else 0 := by simp [twoCapFullOn]
  have hh : (∑ s∈components n L G, (twoCapFullOn n L G (componentVertices n L G s) : ℤ))=
      (twoCapFullCount n L G : ℤ) := by
    simp only [twoCapFullCount,as_sum]
    exact component_sum n L G _
  exact_mod_cast hh

theorem certificate_mixed_degree_four_component_bound {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (degree : ∀ p∈core n L, coreDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) p≤4) :
    let G := fun a => ofPredicate n L (tri a) hL (ht a)
    3*(Fintype.card α : ℤ)+(UpperEdgeInventory.edges n L\usedEdges G).card+
      coreComponentCount n L G+higherSurplus n L≤(n : ℤ)*(n-2)+twoCapFullCount n L G := by
  classical
  let G := fun a => ofPredicate n L (tri a) hL (ht a)
  have hEach (s : (coreGraph n L G).ConnectedComponent) (hs : s∈components n L G) :
      (1 : ℤ)+higherSurplusOn n L (componentVertices n L G s)≤
        (twoCapFullOn n L G (componentVertices n L G s) : ℤ)+componentCost n L G (componentVertices n L G s) :=
    certificate_closed_mixed_degree_four_cost n L hL hn tri hi ht (componentVertices n L G s)
      (component_subset n L G s) (component_nonempty n L G s) (component_closed n L hL tri ht s)
      (fun p hp => degree p (component_subset n L G s hp))
  have hSum := sum_le_sum hEach
  simp only [sum_add_distrib,sum_const,nsmul_eq_mul,mul_one,components_card,component_surplus_sum] at hSum
  have capSumZ : (∑ s∈components n L G, (twoCapFullOn n L G (componentVertices n L G s) : ℤ))=twoCapFullCount n L G := by
    exact_mod_cast component_two_cap_full_sum n L G
  rw [capSumZ] at hSum
  have hid := certificate_component_cost_identity n L hL hn tri hi ht
  dsimp only at hid
  change 3*(Fintype.card α : ℤ)+(UpperEdgeInventory.edges n L\usedEdges G).card+
    coreComponentCount n L G+higherSurplus n L≤(n : ℤ)*(n-2)+twoCapFullCount n L G
  linarith

#print axioms certificate_closed_mixed_degree_four_cost
#print axioms certificate_mixed_degree_four_component_bound
end Kobon.UpperOpenMathMixedDegreeFour
