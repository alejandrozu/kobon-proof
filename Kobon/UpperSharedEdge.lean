import Kobon.FanGeometry

/-!
# A shared triangular side has a multiple endpoint

This is a real-coordinate bridge for upper-bound incidence arguments. If two
triangular interiors are disjoint and have the same side, its two endpoints
cannot both be ordinary intersections. The supports are actual indexed
arrangement lines. This does not enumerate the global elementary edges.
-/
namespace Kobon.UpperSharedEdge
open Cells FanGeometry

/-- Two triangles on a common indexed supporting line, with their common
side consistently named p--q. The remaining supports have explicit indices. -/
structure Pair (n : ℕ) (L : ℕ → Line ℝ) where
  first : TriangleGeometry
  second : TriangleGeometry
  edge : Fin n
  firstA : Fin n
  firstB : Fin n
  secondA : Fin n
  secondB : Fin n
  same_p : second.p=first.p
  same_q : second.q=first.q
  first_edge : first.C=L edge
  second_edge : second.C=L edge
  first_a : first.A=L firstA
  first_b : first.B=L firstB
  second_a : second.A=L secondA
  second_b : second.B=L secondB

namespace Pair
variable {n : ℕ} {L : ℕ → Line ℝ} (f : Pair n L)

theorem firstA_ne_edge : f.firstA≠f.edge := by
  intro h
  apply f.first.Ap
  rw [f.first_a,h,← f.first_edge]
  exact f.first.Cp

theorem firstB_ne_edge : f.firstB≠f.edge := by
  intro h
  apply f.first.Bq
  rw [f.first_b,h,← f.first_edge]
  exact f.first.Cq

theorem secondA_ne_edge : f.secondA≠f.edge := by
  intro h
  apply f.second.Ap
  rw [f.second_a,h,← f.second_edge]
  exact f.second.Cp

theorem secondB_ne_edge : f.secondB≠f.edge := by
  intro h
  apply f.second.Bq
  rw [f.second_b,h,← f.second_edge]
  exact f.second.Cq

theorem first_supports_ne : f.firstA≠f.firstB := by
  intro h
  apply f.first.Ap
  rw [f.first_a,h,← f.first_b]
  exact f.first.Bp

theorem supports_eq_of_ordinary
    (hp : OrdinaryAt n L f.first.p) (hq : OrdinaryAt n L f.first.q) :
    f.firstA=f.secondA ∧ f.firstB=f.secondB := by
  constructor
  · apply ordinary_nonradial_unique n L f.first.q hq f.edge
    · simpa only [f.first_edge] using f.first.Cq
    · simpa only [f.first_a] using f.first.Aq
    · simpa only [f.second_a,f.same_q] using f.second.Aq
    · exact f.firstA_ne_edge
    · exact f.secondA_ne_edge
  · apply ordinary_nonradial_unique n L f.first.p hp f.edge
    · simpa only [f.first_edge] using f.first.Cp
    · simpa only [f.first_b] using f.first.Bp
    · simpa only [f.second_b,f.same_p] using f.second.Bp
    · exact f.firstB_ne_edge
    · exact f.secondB_ne_edge

/-- Ordinary common endpoints force the third vertices to coincide. -/
theorem apex_eq_of_ordinary (hL : NoParallel n L)
    (hp : OrdinaryAt n L f.first.p) (hq : OrdinaryAt n L f.first.q) :
    f.first.r=f.second.r := by
  obtain ⟨ha,hb⟩ := f.supports_eq_of_ordinary hp hq
  apply two_lines_two_points (L f.firstA) (L f.firstB)
  · exact noParallel_any n L hL f.firstA f.firstB
      f.firstA.isLt f.firstB.isLt (fun h => f.first_supports_ne (Fin.ext h))
  · simpa only [f.first_a] using f.first.Ar
  · simpa only [f.second_a,← ha] using f.second.Ar
  · simpa only [f.first_b] using f.first.Br
  · simpa only [f.second_b,← hb] using f.second.Br

/-- A common side of two disjoint real triangular interiors cannot have
two ordinary endpoints. No count of edges is assumed in this theorem. -/
theorem not_both_endpoints_ordinary (hL : NoParallel n L)
    (hdisjoint : Disjoint f.first.interior f.second.interior) :
    ¬(OrdinaryAt n L f.first.p ∧ OrdinaryAt n L f.first.q) := by
  rintro ⟨hp,hq⟩
  have hr := f.apex_eq_of_ordinary hL hp hq
  have hi : f.first.interior=f.second.interior := by
    simp only [TriangleGeometry.interior,f.same_p,f.same_q,← hr]
  obtain ⟨x,hx⟩ := interior_nonempty f.first
  exact Set.disjoint_left.mp hdisjoint hx (hi ▸ hx)

theorem has_nonordinary_endpoint (hL : NoParallel n L)
    (hdisjoint : Disjoint f.first.interior f.second.interior) :
    ¬OrdinaryAt n L f.first.p ∨ ¬OrdinaryAt n L f.first.q := by
  exact not_and_or.mp (f.not_both_endpoints_ordinary hL hdisjoint)

end Pair

/-- At a point already incident to two distinct indexed lines, failure of
the ordinary-point predicate supplies an actual third incident support. -/
theorem third_support_of_not_ordinary (n : ℕ) (L : ℕ → Line ℝ) (p : Point)
    (a b : Fin n) (hab : a≠b)
    (ha : affineEval (L a) p=0) (hb : affineEval (L b) p=0)
    (ho : ¬OrdinaryAt n L p) :
    ∃ c : Fin n, c≠a ∧ c≠b ∧ affineEval (L c) p=0 := by
  classical
  by_contra hc
  apply ho
  refine ⟨a,b,hab,?_⟩
  intro i
  constructor
  · intro hi
    by_contra h
    have hia : i≠a := fun he => h (Or.inl he)
    have hib : i≠b := fun he => h (Or.inr he)
    exact hc ⟨i,hia,hib,hi⟩
  · rintro (rfl|rfl)
    · exact ha
    · exact hb

#print axioms Pair.apex_eq_of_ordinary
#print axioms Pair.has_nonordinary_endpoint
#print axioms third_support_of_not_ordinary
end Kobon.UpperSharedEdge
