import Kobon.UpperOpenMathMixedCurvature

/-! Degree-free component bounds for every actual intersection multiplicity.
Two-cap full triple corrections are counted once. One-cap full corrections
are rounded in pairs inside each actual connected component. -/
namespace Kobon.UpperOpenMathMixedCurvatureBound
open Cells FanGeometry UpperVertexBudget UpperTriangleIncidence UpperSharedIncidence
  UpperCoreExtraction UpperOpenMathCapHeavyTriples UpperOpenMathCoreComponents
  UpperOpenMathMixedDegreeThree UpperOpenMathMixedDegreeFour UpperOpenMathMixedCurvature Finset
open scoped BigOperators
set_option maxHeartbeats 1000000

theorem certificate_closed_mixed_rounded_cost {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (P : Finset Point) (sub : P⊆core n L) (nonempty : P.Nonempty)
    (closed : SharedCoreClosed n L (fun a => ofPredicate n L (tri a) hL (ht a)) P) :
    let G := fun a => ofPredicate n L (tri a) hL (ht a)
    1+higherSurplusOn n L P≤componentCost n L G P+twoCapFullOn n L G P+
      ((oneCapFullOn n L G P+1)/2 : ℕ) := by
  let G := fun a => ofPredicate n L (tri a) hL (ht a)
  have strict := certificate_closed_mixed_paid_positive n L hL hn tri hi ht P sub nonempty closed
  have rounding : oneCapFullOn n L G P≤2*((oneCapFullOn n L G P+1)/2) := by omega
  have roundingZ : (oneCapFullOn n L G P : ℤ)≤2*((((oneCapFullOn n L G P+1)/2) : ℕ) : ℤ) := by
    exact_mod_cast rounding
  dsimp only at strict ⊢
  omega

theorem component_one_cap_full_sum {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (G : α → TriangleGeometry) :
    (∑ s∈components n L G, (oneCapFullOn n L G (componentVertices n L G s) : ℤ))=
      oneCapFullCount n L G := by
  classical
  have as_sum (Q : Finset Point) : (oneCapFullOn n L G Q : ℤ)=
      ∑ p∈Q, if (supports n L p).card=3 ∧ ordinaryDegree n L G p=1 ∧ coreDegree n L G p=5
        then (1 : ℤ) else 0 := by simp [oneCapFullOn]
  simp only [oneCapFullCount,as_sum]
  exact component_sum n L G _

theorem certificate_mixed_curvature_component_bound {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a)) :
    let G := fun a => ofPredicate n L (tri a) hL (ht a)
    3*(Fintype.card α : ℤ)+(UpperEdgeInventory.edges n L\usedEdges G).card+
      coreComponentCount n L G+higherSurplus n L≤(n : ℤ)*(n-2)+
      twoCapFullCount n L G+componentOneCapHalf n L G := by
  classical
  let G := fun a => ofPredicate n L (tri a) hL (ht a)
  have each (s : (coreGraph n L G).ConnectedComponent) (hs : s∈components n L G) :=
    certificate_closed_mixed_rounded_cost n L hL hn tri hi ht (componentVertices n L G s)
      (component_subset n L G s) (component_nonempty n L G s) (component_closed n L hL tri ht s)
  have total := sum_le_sum each
  simp only [sum_add_distrib,sum_const,nsmul_eq_mul,mul_one,components_card,component_surplus_sum] at total
  have twoSum : (∑ s∈components n L G, (twoCapFullOn n L G (componentVertices n L G s) : ℤ))=
      twoCapFullCount n L G := by exact_mod_cast component_two_cap_full_sum n L G
  have halfSum : (∑ s∈components n L G,
      ((((oneCapFullOn n L G (componentVertices n L G s)+1)/2) : ℕ) : ℤ))=
      componentOneCapHalf n L G := by
    exact_mod_cast (rfl : (∑ s∈components n L G,
      (oneCapFullOn n L G (componentVertices n L G s)+1)/2)=componentOneCapHalf n L G)
  rw [twoSum,halfSum] at total
  have identity := certificate_component_cost_identity n L hL hn tri hi ht
  dsimp only at identity ⊢
  linarith

theorem certificate_mixed_doubled_component_bound {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a)) :
    let G := fun a => ofPredicate n L (tri a) hL (ht a)
    6*(Fintype.card α : ℤ)+2*(UpperEdgeInventory.edges n L\usedEdges G).card+
      coreComponentCount n L G+2*higherSurplus n L≤2*(n : ℤ)*(n-2)+
      2*twoCapFullCount n L G+oneCapFullCount n L G := by
  classical
  let G := fun a => ofPredicate n L (tri a) hL (ht a)
  have each (s : (coreGraph n L G).ConnectedComponent) (hs : s∈components n L G) :=
    certificate_closed_mixed_paid_positive n L hL hn tri hi ht (componentVertices n L G s)
      (component_subset n L G s) (component_nonempty n L G s) (component_closed n L hL tri ht s)
  have total := sum_le_sum each
  simp only [sum_add_distrib,sum_sub_distrib,← mul_sum,sum_const,nsmul_eq_mul,mul_one,
    components_card,component_surplus_sum] at total
  have twoSum : (∑ s∈components n L G, (twoCapFullOn n L G (componentVertices n L G s) : ℤ))=
      twoCapFullCount n L G := by exact_mod_cast component_two_cap_full_sum n L G
  have oneSum : (∑ s∈components n L G, (oneCapFullOn n L G (componentVertices n L G s) : ℤ))=
      oneCapFullCount n L G := component_one_cap_full_sum n L G
  rw [twoSum,oneSum] at total
  have identity := certificate_component_cost_identity n L hL hn tri hi ht
  dsimp only at identity ⊢
  linarith

#print axioms certificate_closed_mixed_rounded_cost
#print axioms certificate_mixed_curvature_component_bound
#print axioms certificate_mixed_doubled_component_bound
end Kobon.UpperOpenMathMixedCurvatureBound
