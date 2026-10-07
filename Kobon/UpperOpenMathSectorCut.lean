import Kobon.UpperOpenMathRadialOrder
import Kobon.UpperFanSupport

/-!
# Certified triangle sectors contain no intermediate incident ray

The empty-triangle weak-side predicate rules out every incident arrangement
line whose direction lies strictly between the triangle's two outward sides.
This gives the actual geometric exclusion needed to identify occupied
consecutive sectors after canonical ray sorting.
-/
namespace Kobon.UpperOpenMathSectorCut
open Cells FanGeometry

theorem affine_cone_identity (l : Line ℝ) (c q v r : Point) :
    areaDet c v r*(affineEval l q-affineEval l c)+
      areaDet c q v*(affineEval l r-affineEval l c)=
      areaDet c q r*(affineEval l v-affineEval l c) := by
  dsimp [areaDet,affineEval]
  ring

/-- A valid line through the triangle's center and an intermediate outward
direction would cut its interior. The proof uses exact affine determinant
identities and the weak-side predicate, without an angle convention. -/
theorem no_intermediate_ray (t : TriangleGeometry) (l : Line ℝ) (v : Point)
    (valid : l.a≠0 ∨ l.b≠0) (center_on : affineEval l t.p=0)
    (ray_on : affineEval l v=0) (weak : WeakSide l t.p t.q t.r)
    (left : 0<areaDet t.p t.q v) (right : 0<areaDet t.p v t.r) : False := by
  have hid := affine_cone_identity l t.p t.q v t.r
  rw [center_on,ray_on,sub_zero,sub_zero,sub_self,mul_zero] at hid
  have hq : affineEval l t.q=0 := by
    rcases weak with ⟨_,hq,hr⟩|⟨_,hq,hr⟩
    · have h₁ := mul_nonneg right.le hq
      have h₂ := mul_nonneg left.le hr
      have hz : areaDet t.p v t.r*affineEval l t.q=0 := by linarith
      exact (mul_eq_zero.mp hz).resolve_left right.ne'
    · have h₁ := mul_nonpos_of_nonneg_of_nonpos right.le hq
      have h₂ := mul_nonpos_of_nonneg_of_nonpos left.le hr
      have hz : areaDet t.p v t.r*affineEval l t.q=0 := by linarith
      exact (mul_eq_zero.mp hz).resolve_left right.ne'
  have hr : affineEval l t.r=0 := by
    rw [hq,mul_zero,zero_add] at hid
    exact (mul_eq_zero.mp hid).resolve_left left.ne'
  obtain ⟨ha,hb⟩ := three_zeros_force_zero_normal l t.p t.q t.r
    t.nondegenerate center_on hq hr
  exact valid.elim (fun h => h ha) (fun h => h hb)

theorem certificate_no_intermediate_ray (n : ℕ) (L : ℕ → Line ℝ)
    (hL : NoParallel n L) (tri : Triple) (ht : TrianglePredicate n L tri)
    (i : Fin n) (v : Point)
    (center_on : affineEval (L i) (ofPredicate n L tri hL ht).p=0)
    (ray_on : affineEval (L i) v=0)
    (left : 0<areaDet (ofPredicate n L tri hL ht).p
      (ofPredicate n L tri hL ht).q v)
    (right : 0<areaDet (ofPredicate n L tri hL ht).p v
      (ofPredicate n L tri hL ht).r) : False := by
  have hn : 2≤n := by have := ht.1; have := ht.2.1; have := ht.2.2.1; omega
  exact no_intermediate_ray (ofPredicate n L tri hL ht) (L i) v
    (line_valid n L hL hn i) center_on ray_on
    (weakSide_of_predicate n L tri hL ht i) left right

/-- Once a triangle's apex is the selected real point, the canonical
positive or negative representative of each incident line cannot lie
strictly inside its outward sector. -/
theorem ordered_no_intermediate_ray (n : ℕ) (L : ℕ → Line ℝ)
    (hL : NoParallel n L) (hn : 2≤n) (c : Point)
    (D : UpperOpenMathRadialOrder.OrderedDirections n L (UpperVertexBudget.supports n L c))
    (t : TriangleGeometry) (center : t.p=c)
    (weak : ∀ i : Fin n, WeakSide (L i) t.p t.q t.r)
    (k : Fin (UpperVertexBudget.supports n L c).card) (scale : ℝ)
    (left : 0<areaDet c t.q (D.outerPoint c k scale))
    (right : 0<areaDet c (D.outerPoint c k scale) t.r) : False := by
  let i := D.radial k
  have hcenter : affineEval (L i) c=0 := by
    have hm := D.radial_mem k
    exact (Finset.mem_filter.mp hm).2
  have hpoint := D.outerPoint_on_line c
    (fun j hj => (Finset.mem_filter.mp hj).2) k scale
  apply no_intermediate_ray t (L i) (D.outerPoint c k scale)
    (line_valid n L hL hn i)
  · simpa only [center] using hcenter
  · exact hpoint
  · exact weak i
  · simpa only [center] using left
  · simpa only [center] using right

#print axioms no_intermediate_ray
#print axioms certificate_no_intermediate_ray
#print axioms ordered_no_intermediate_ray
end Kobon.UpperOpenMathSectorCut
