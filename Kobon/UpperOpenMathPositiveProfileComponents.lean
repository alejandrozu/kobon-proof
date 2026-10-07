import Kobon.UpperOpenMathClosedN12Curvature

/-! A sufficient profile condition for a strict contribution from every
shared-core component. The profile condition is explicit; no claim that all
arrangements satisfy it is made. -/
namespace Kobon.UpperOpenMathPositiveProfileComponents
open Cells FanGeometry UpperVertexBudget UpperTriangleIncidence UpperSharedIncidence
  UpperCoreExtraction UpperOpenMathCapHeavyTriples UpperOpenMathCoreComponents
  UpperOpenMathAntipodalAdjacency Finset
open scoped BigOperators

noncomputable def PositiveProfile {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (G : α → TriangleGeometry) (P : Finset Point) : Prop :=
  (P.filter (fun p => ordinaryDegree n L G p=1 ∧ coreDegree n L G p=5)).card+1 ≤
    3*(P.filter (fun p => ordinaryDegree n L G p=3)).card+
    3*(P.filter (fun p => ordinaryDegree n L G p=2 ∧ coreDegree n L G p=1)).card+
    (P.filter (fun p => ordinaryDegree n L G p=1 ∧ coreDegree n L G p=2)).card

theorem certificate_positive_profile_cost {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (triples : ∀ p∈core n L, (supports n L p).card=3)
    (P : Finset Point) (sub : P⊆core n L)
    (closed : SharedCoreClosed n L (fun a=>ofPredicate n L (tri a) hL (ht a)) P)
    (profile : PositiveProfile n L (fun a=>ofPredicate n L (tri a) hL (ht a)) P) :
    1≤componentCost n L (fun a=>ofPredicate n L (tri a) hL (ht a)) P := by
  classical
  let G := fun a=>ofPredicate n L (tri a) hL (ht a)
  let B := (P.filter (fun p=>ordinaryDegree n L G p=1 ∧ coreDegree n L G p=5)).card
  let E := (P.filter (fun p=>ordinaryDegree n L G p=3)).card
  let Q := (P.filter (fun p=>ordinaryDegree n L G p=2 ∧ coreDegree n L G p=1)).card
  let R := (P.filter (fun p=>ordinaryDegree n L G p=1 ∧ coreDegree n L G p=2)).card
  change B+1≤3*E+3*Q+R at profile
  have castProfile : (B : ℤ)+1≤3*(E : ℤ)+3*(Q : ℤ)+(R : ℤ) := by
    exact_mod_cast profile
  have gain := UpperOpenMathClosedN12Curvature.certificate_closed_n12_source_free_gain
    n L hL hn tri hi ht triples P sub closed
  change 0≤2*componentCost n L G P+(B : ℤ)-3*(E : ℤ)-3*(Q : ℤ)-(R : ℤ) at gain
  change 1≤componentCost n L G P
  omega

theorem certificate_positive_profile_component_defect {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (triples : ∀ p∈core n L, (supports n L p).card=3)
    (profiles : ∀ s∈components n L (fun a=>ofPredicate n L (tri a) hL (ht a)),
      PositiveProfile n L (fun a=>ofPredicate n L (tri a) hL (ht a))
        (componentVertices n L (fun a=>ofPredicate n L (tri a) hL (ht a)) s)) :
    let G := fun a=>ofPredicate n L (tri a) hL (ht a)
    ((UpperEdgeInventory.edges n L\usedEdges G).card : ℤ)+(components n L G).card ≤
      (n : ℤ)*(n-2)-3*Fintype.card α := by
  classical
  let G := fun a=>ofPredicate n L (tri a) hL (ht a)
  have each (s : (coreGraph n L G).ConnectedComponent) (hs : s∈components n L G) :
      (1 : ℤ)≤componentCost n L G (componentVertices n L G s) :=
    certificate_positive_profile_cost n L hL hn tri hi ht triples
      (componentVertices n L G s) (component_subset n L G s)
      (component_closed n L hL tri ht s) (profiles s hs)
  have summed := sum_le_sum each
  have identity := certificate_component_cost_identity n L hL hn tri hi ht
  simp only [sum_const, nsmul_eq_mul, mul_one] at summed
  dsimp only at identity ⊢
  linarith

#print axioms certificate_positive_profile_cost
#print axioms certificate_positive_profile_component_defect
end Kobon.UpperOpenMathPositiveProfileComponents
