import Kobon.UpperOpenMathMixedDegreeThreeResources
import Kobon.UpperOpenMathMixedDegreeThreeWeights

/-!
# Mixed multiplicities with at most three shared core neighbors

Every actual nonempty shared-core component contributes one defect unit,
plus `r*(r-4)` at each vertex of multiplicity at least four. The only
potential equality cluster consists of extremal fans and contradicts a
finite supporting half-plane. The balanced triple cluster is excluded by
the verified three-fan cycle obstruction.
-/
namespace Kobon.UpperOpenMathMixedDegreeThree
open Cells FanGeometry UpperVertexBudget UpperTriangleIncidence UpperSharedIncidence
  UpperCoreExtraction UpperOpenMathCapHeavyTriples UpperOpenMathCoreComponents
  UpperOpenMathActualFans Finset
open scoped BigOperators

noncomputable def higherSurplusOn (n : ℕ) (L : ℕ → Line ℝ) (P : Finset Point) : ℤ := by
  classical
  exact ∑ p∈P.filter (fun p => 4≤(supports n L p).card),
    (supports n L p).card*((supports n L p).card-4 : ℤ)

noncomputable def higherSurplus (n : ℕ) (L : ℕ → Line ℝ) : ℤ :=
  higherSurplusOn n L (core n L)

theorem certificate_closed_mixed_degree_three_cost {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (P : Finset Point) (sub : P⊆core n L) (nonempty : P.Nonempty)
    (closed : SharedCoreClosed n L (fun a => ofPredicate n L (tri a) hL (ht a)) P)
    (degree : ∀ p∈P, coreDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) p≤3) :
    1+higherSurplusOn n L P≤componentCost n L (fun a => ofPredicate n L (tri a) hL (ht a)) P := by
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
  have hd : ∀ p∈P, d p≤3 := degree
  have hfive (p : Point) (hp : p∈P) (hpR : r p=3) : a p+d p≠5 :=
    UpperOpenMathTripleDegreeThree.certificate_triple_not_five n L hL hn tri hi ht p (sub hp) hpR
  have hext (p : Point) (hp : p∈P) (hpR : r p=3) (hpA : a p=3) : d p=3 := by
    have hx : 2*(supports n L p).card-3≤ordinaryDegree n L G p := by
      change 2*r p-3≤a p
      rw [hpR,hpA]
    exact UpperOpenMathSupportedCores.certificate_extremal_neighbor_count n L hL hn tri hi ht p (sub hp) hx
  have counts := UpperOpenMathMixedDegreeThreeResources.closed_mixed_extremal_counts n L hL hn tri hi ht P sub closed
  change (∑ p∈E, d p)=3*E.card ∧ 3*E.card≤(∑ p∈B, d p)+(∑ p∈H, d p) at counts
  have discharge := UpperOpenMathMixedDegreeThreeWeights.finite_mixed_weight_rigidity
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
  have identity : (∑ p∈P, W p)=2*(componentCost n L G P-higherSurplusOn n L P) := by
    change (∑ p∈P, W p)=2*((∑ p∈P, (r p : ℤ)*(r p-2))-
      (∑ p∈P, (a p : ℤ))-(componentEdges n L G P).card-higherSurplusOn n L P)
    rw [sum_congr rfl (fun p _ => each p)]
    simp only [sum_sub_distrib]
    rw [sumLoss,← mul_sum,dsum,sumHigher]
    ring
  have nonneg : 0≤componentCost n L G P-higherSurplusOn n L P := by
    have hh := discharge.1
    change 0≤∑ p∈P, W p at hh
    rw [identity] at hh
    omega
  have nozero : componentCost n L G P-higherSurplusOn n L P≠0 := by
    intro hz
    have wzero : (∑ p∈P, W p)=0 := by rw [identity,hz]; ring
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
    have extremal (p : Point) (hp : p∈X) : a p=2*r p-3 := by
      rcases mem_union.mp hp with hpE|hpH
      · obtain ⟨hpP,hpR,hpA⟩ := mem_filter.mp hpE
        rw [hpR,hpA]
      · obtain ⟨hpP,hpR⟩ := mem_filter.mp hpH
        exact (high p hpP hpR).1
    by_cases xNonempty : X.Nonempty
    · exact UpperOpenMathClosedExtremal.certificate_closed_extremal_impossible
        n L hL hn tri hi ht X xSub xNonempty xClosed extremal
    · have xEmpty : X=∅ := not_nonempty_iff_eq_empty.mp xNonempty
      have eEmpty : E=∅ := (union_eq_empty.mp xEmpty).1
      have hEmpty : H=∅ := (union_eq_empty.mp xEmpty).2
      have rigid (p : Point) (hp : p∈P) : r p=3 ∧ a p=2 ∧ d p=2 := by
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
      exact UpperOpenMathTwoTwoCore.certificate_closed_two_two_impossible
        n L hL hn tri hi ht P sub nonempty closed rigid
  change 1+higherSurplusOn n L P≤componentCost n L G P
  omega

theorem component_surplus_sum {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (G : α → TriangleGeometry) :
    (∑ s∈components n L G, higherSurplusOn n L (componentVertices n L G s))=higherSurplus n L := by
  classical
  simp only [higherSurplusOn,higherSurplus,sum_filter]
  rw [component_sum]

theorem certificate_mixed_degree_three_component_bound {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (degree : ∀ p∈core n L, coreDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) p≤3) :
    let G := fun a => ofPredicate n L (tri a) hL (ht a)
    3*(Fintype.card α : ℤ)+(UpperEdgeInventory.edges n L\usedEdges G).card+
      coreComponentCount n L G+higherSurplus n L≤(n : ℤ)*(n-2) := by
  classical
  let G := fun a => ofPredicate n L (tri a) hL (ht a)
  have hEach (s : (coreGraph n L G).ConnectedComponent) (hs : s∈components n L G) :
      (1 : ℤ)+higherSurplusOn n L (componentVertices n L G s)≤
        componentCost n L G (componentVertices n L G s) :=
    certificate_closed_mixed_degree_three_cost n L hL hn tri hi ht (componentVertices n L G s)
      (component_subset n L G s) (component_nonempty n L G s) (component_closed n L hL tri ht s)
      (fun p hp => degree p (component_subset n L G s hp))
  have hSum := sum_le_sum hEach
  simp only [sum_add_distrib,sum_const,nsmul_eq_mul,mul_one,components_card,component_surplus_sum] at hSum
  have hid := certificate_component_cost_identity n L hL hn tri hi ht
  dsimp only at hid
  change 3*(Fintype.card α : ℤ)+(UpperEdgeInventory.edges n L\usedEdges G).card+
    coreComponentCount n L G+higherSurplus n L≤(n : ℤ)*(n-2)
  linarith

#print axioms certificate_closed_mixed_degree_three_cost
#print axioms certificate_mixed_degree_three_component_bound
end Kobon.UpperOpenMathMixedDegreeThree
