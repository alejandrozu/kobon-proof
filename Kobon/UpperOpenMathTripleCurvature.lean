import Kobon.UpperOpenMathTripleZeroCurvature
import Kobon.UpperOpenMathMixedCapBudget

/-! Quantitative all-triple core correction without a degree restriction.
Only full nonextremal fans of types (2,4) and (1,5) enter the correction.
Every local datum is derived from the actual selected triangle certificate.
The theorem does not assert that the correction vanishes in all arrangements. -/
namespace Kobon.UpperOpenMathTripleCurvature
open Cells FanGeometry UpperVertexBudget UpperTriangleIncidence
  UpperSharedIncidence UpperCoreExtraction UpperOpenMathCapHeavyTriples
  UpperOpenMathCoreComponents UpperOpenMathTripleCurvatureWeights Finset
open scoped BigOperators
set_option maxHeartbeats 1000000

noncomputable def badCurvatureOn {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (G : α → TriangleGeometry) (P : Finset Point) : ℤ :=
  ∑ p∈P, badWeight (ordinaryDegree n L G p) (coreDegree n L G p)

noncomputable def badCurvature {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (G : α → TriangleGeometry) : ℤ :=
  badCurvatureOn n L G (core n L)

theorem badWeight_nonnegative (a d : ℕ) : 0≤badWeight a d := by
  unfold badWeight
  split_ifs <;> norm_num

theorem badCurvatureOn_counts {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (G : α → TriangleGeometry) (P : Finset Point) :
    badCurvatureOn n L G P=
      2*((P.filter (fun p => ordinaryDegree n L G p=2 ∧ coreDegree n L G p=4)).card : ℤ)+
      ((P.filter (fun p => ordinaryDegree n L G p=1 ∧ coreDegree n L G p=5)).card : ℤ) := by
  classical
  have he (a d : ℕ) : badWeight a d=
      2*(if a=2 ∧ d=4 then (1 : ℤ) else 0)+(if a=1 ∧ d=5 then 1 else 0) := by
    unfold badWeight
    split_ifs <;> omega
  unfold badCurvatureOn
  simp_rw [he]
  simp only [sum_add_distrib,← mul_sum,sum_ite,sum_const_zero,add_zero,
    sum_const,nsmul_eq_mul,mul_one]

theorem closed_curvature_identity {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (G : α → TriangleGeometry) (P : Finset Point)
    (closed : SharedCoreClosed n L G P)
    (triples : ∀ p∈P, (supports n L p).card=3) :
    2*componentCost n L G P=
      ∑ p∈P, (6-2*(ordinaryDegree n L G p : ℤ)-coreDegree n L G p) := by
  classical
  have hsum : (∑ p∈P, (coreDegree n L G p : ℤ))=2*((componentEdges n L G P).card : ℤ) := by
    exact_mod_cast closed_degree_sum n L G P closed
  have hr : (∑ p∈P, (supports n L p).card*((supports n L p).card-2 : ℤ))=3*(P.card : ℤ) := by
    calc
      _=∑ _p∈P, (3 : ℤ) := sum_congr rfl (by intro p hp; rw [triples p hp]; norm_num)
      _=_ := by simp [mul_comm]
  rw [componentCost,hr]
  simp only [sum_sub_distrib,← mul_sum,sum_const,nsmul_eq_mul]
  rw [hsum]
  ring

theorem certificate_closed_curvature_data {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (P : Finset Point) (sub : P⊆core n L)
    (closed : SharedCoreClosed n L (fun a => ofPredicate n L (tri a) hL (ht a)) P)
    (triples : ∀ p∈P, (supports n L p).card=3) :
    let G := fun a => ofPredicate n L (tri a) hL (ht a)
    0≤2*componentCost n L G P+badCurvatureOn n L G P ∧
    (badCurvatureOn n L G P=0 → componentCost n L G P=0 →
      ∀ p∈P, (ordinaryDegree n L G p=2 ∧ coreDegree n L G p=2) ∨
        (ordinaryDegree n L G p=0 ∧ coreDegree n L G p=6)) := by
  classical
  let G := fun a => ofPredicate n L (tri a) hL (ht a)
  let a := ordinaryDegree n L G
  let d := coreDegree n L G
  have ha (p : Point) (hp : p∈P) : a p≤3 := by
    have hh := UpperOpenMathActualFans.certificate_local_fan_bound n L hL hn tri hi ht p (sub hp)
    rw [triples p hp] at hh
    exact hh
  have had (p : Point) (hp : p∈P) : a p+d p≤6 := by
    have hh := UpperOpenMathMixedCapBudget.certificate_local_combined_degree n L hL hn tri hi ht p (sub hp)
    rw [triples p hp] at hh
    exact hh
  have hfive (p : Point) (hp : p∈P) : a p+d p≠5 :=
    UpperOpenMathTripleDegreeThree.certificate_triple_not_five n L hL hn tri hi ht p (sub hp) (triples p hp)
  have hext (p : Point) (hp : p∈P) (hpA : a p=3) : d p=3 := by
    have he : 2*(supports n L p).card-3≤ordinaryDegree n L G p := by
      change 2*(supports n L p).card-3≤a p
      rw [triples p hp,hpA]
    exact UpperOpenMathSupportedCores.certificate_extremal_neighbor_count n L hL hn tri hi ht p (sub hp) he
  have capacity := UpperOpenMathTripleDegreeThree.closed_extremal_capacity n L hL hn tri hi ht P sub closed triples
  have discharge := finite_curvature_discharge P a d ha had hfive hext capacity
  have identity := closed_curvature_identity n L G P closed triples
  have paid : (∑ p∈P, (6-2*(a p : ℤ)-d p+badWeight (a p) (d p)))=
      2*componentCost n L G P+badCurvatureOn n L G P := by
    rw [sum_add_distrib,← identity]
    rfl
  change 0≤2*componentCost n L G P+badCurvatureOn n L G P ∧ _
  refine ⟨by rw [← paid]; exact discharge.1,?_⟩
  intro hbad hcost p hp
  have hw : (∑ p∈P, (6-2*(a p : ℤ)-d p+badWeight (a p) (d p)))=0 := by rw [paid,hbad,hcost]; ring
  have hbzero : ∀ p∈P, badWeight (a p) (d p)=0 :=
    (sum_eq_zero_iff_of_nonneg (fun p _ => badWeight_nonnegative (a p) (d p))).mp hbad
  have hgood : ¬(a p=2 ∧ d p=4) ∧ ¬(a p=1 ∧ d p=5) := by
    have hz := hbzero p hp
    unfold badWeight at hz
    split_ifs at hz <;> omega
  rcases discharge.2 hw p hp with h|h|h|h
  · exact Or.inl h
  · exact Or.inr h
  · exact False.elim (hgood.1 h)
  · exact False.elim (hgood.2 h)

theorem certificate_closed_curvature_bound {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (P : Finset Point) (sub : P⊆core n L) (nonempty : P.Nonempty)
    (closed : SharedCoreClosed n L (fun a => ofPredicate n L (tri a) hL (ht a)) P)
    (triples : ∀ p∈P, (supports n L p).card=3) :
    let G := fun a => ofPredicate n L (tri a) hL (ht a)
    1≤componentCost n L G P+badCurvatureOn n L G P := by
  classical
  let G := fun a => ofPredicate n L (tri a) hL (ht a)
  have data := certificate_closed_curvature_data n L hL hn tri hi ht P sub closed triples
  change 0≤2*componentCost n L G P+badCurvatureOn n L G P ∧ _ at data
  have hnonneg : 0≤badCurvatureOn n L G P := sum_nonneg (fun p _ => badWeight_nonnegative _ _)
  change 1≤componentCost n L G P+badCurvatureOn n L G P
  by_cases hz : badCurvatureOn n L G P=0
  · have nozero : componentCost n L G P≠0 := by
      intro hc
      exact UpperOpenMathTripleZeroCurvature.certificate_closed_zero_types_impossible
        n L hL hn tri hi ht P sub nonempty closed triples (data.2 hz hc)
    omega
  · omega

theorem component_curvature_sum {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (G : α → TriangleGeometry) :
    (∑ s∈components n L G, badCurvatureOn n L G (componentVertices n L G s))=
      badCurvature n L G := by
  classical
  exact component_sum n L G _

theorem certificate_triple_curvature_upper {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (triples : ∀ p∈core n L, (supports n L p).card=3) :
    let G := fun a => ofPredicate n L (tri a) hL (ht a)
    3*(Fintype.card α : ℤ)+(UpperEdgeInventory.edges n L\usedEdges G).card+
      coreComponentCount n L G≤(n : ℤ)*(n-2)+badCurvature n L G := by
  classical
  let G := fun a => ofPredicate n L (tri a) hL (ht a)
  have hEach (s : (coreGraph n L G).ConnectedComponent) (hs : s∈components n L G) :
      (1 : ℤ)≤componentCost n L G (componentVertices n L G s)+
        badCurvatureOn n L G (componentVertices n L G s) :=
    certificate_closed_curvature_bound n L hL hn tri hi ht (componentVertices n L G s)
      (component_subset n L G s) (component_nonempty n L G s) (component_closed n L hL tri ht s)
      (fun p hp => triples p (component_subset n L G s hp))
  have hSum := sum_le_sum hEach
  simp only [sum_add_distrib,sum_const,nsmul_eq_mul,mul_one,components_card,component_curvature_sum] at hSum
  have hid := certificate_component_cost_identity n L hL hn tri hi ht
  dsimp only at hid
  change 3*(Fintype.card α : ℤ)+(UpperEdgeInventory.edges n L\usedEdges G).card+
    coreComponentCount n L G≤(n : ℤ)*(n-2)+badCurvature n L G
  linarith

#print axioms certificate_closed_curvature_data
#print axioms certificate_closed_curvature_bound
#print axioms certificate_triple_curvature_upper
end Kobon.UpperOpenMathTripleCurvature
