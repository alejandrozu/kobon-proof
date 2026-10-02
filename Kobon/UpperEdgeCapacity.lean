import Kobon.Cells
import Mathlib.Data.Finset.Card

/-!
# At most two disjoint triangular cells can share a side

This is a coordinate-geometric edge-capacity theorem. No bound on the
number of cells incident to an edge is assumed: it follows from overlap of
two triangles lying on the same side of their common base.
-/
namespace Kobon.UpperEdgeCapacity
open Cells Finset

theorem weightU_segment (p q r x y : Point) (u : ℝ) :
    weightU p q r (segmentPoint x y u)=
      (1-u)*weightU p q r x+u*weightU p q r y := by
  dsimp [weightU,segmentPoint,areaDet]
  ring

theorem weightV_segment (p q r x y : Point) (u : ℝ) :
    weightV p q r (segmentPoint x y u)=
      (1-u)*weightV p q r x+u*weightV p q r y := by
  dsimp [weightV,segmentPoint,areaDet]
  ring

theorem weightW_segment (p q r x y : Point) (u : ℝ) :
    weightW p q r (segmentPoint x y u)=
      (1-u)*weightW p q r x+u*weightW p q r y := by
  dsimp [weightW,segmentPoint,areaDet]
  ring

theorem midpoint_weights (p q r : Point) (ha : areaDet p q r≠0) :
    weightU p q r (segmentPoint p q (1/2))=1/2 ∧
    weightV p q r (segmentPoint p q (1/2))=1/2 ∧
    weightW p q r (segmentPoint p q (1/2))=0 := by
  have hm : segmentPoint p q (1/2)=barycenter p q r (1/2) (1/2) 0 := by
    apply Prod.ext <;> dsimp [segmentPoint,barycenter] <;> ring
  rw [hm]
  exact weights_barycenter p q r ha _ _ _ (by norm_num)

/-- An explicit positive movement from the base midpoint can preserve both
other strictly positive barycentric coordinates. -/
theorem small_step (a b : ℝ) : ∃ u : ℝ, 0<u ∧ u<1 ∧
    0<(1-u)/2+u*a ∧ 0<(1-u)/2+u*b := by
  let M := |a|+|b|+1
  have hM : 0<M := by dsimp [M]; positivity
  let u := 1/(4*M)
  have hu : 0<u := by dsimp [u]; positivity
  have he : (4*M)*u=1 := by dsimp [u]; field_simp
  have hMa : 0≤|a|+a := by have := neg_abs_le a; linarith
  have hMb : 0≤|b|+b := by have := neg_abs_le b; linarith
  have hM1 : 1≤M := by dsimp [M]; linarith [abs_nonneg a,abs_nonneg b]
  have h1 : u<1 := by nlinarith
  have ha : 0<(1-u)/2+u*a := by
    have hz : 0<u*(2*M-1+2*a) := mul_pos hu (by dsimp [M]; nlinarith [abs_nonneg b])
    nlinarith
  have hb : 0<(1-u)/2+u*b := by
    have hz : 0<u*(2*M-1+2*b) := mul_pos hu (by dsimp [M]; nlinarith [abs_nonneg a])
    nlinarith
  exact ⟨u,hu,h1,ha,hb⟩

/-- Two triangles with a common base overlap if their third vertices lie on
the same side of that base. The side condition is expressed as a positive
barycentric coordinate in the first triangle. -/
theorem overlap_of_positive_weight (t s : TriangleGeometry)
    (hp : s.p=t.p) (hq : s.q=t.q)
    (hw : 0<weightW t.p t.q t.r s.r) :
    ∃ x : Point, x∈t.interior ∧ x∈s.interior := by
  obtain ⟨u,hu,hu1,hU,hV⟩ := small_step
    (weightU t.p t.q t.r s.r) (weightV t.p t.q t.r s.r)
  let m := segmentPoint t.p t.q (1/2)
  let x := segmentPoint m s.r u
  have hm := midpoint_weights t.p t.q t.r t.nondegenerate
  refine ⟨x,?_,?_⟩
  · apply (t.open_weights x).mpr
    dsimp [x,m]
    rw [weightU_segment,weightV_segment,weightW_segment,hm.1,hm.2.1,hm.2.2]
    refine ⟨?_,?_,?_⟩
    · nlinarith
    · nlinarith
    · simpa using mul_pos hu hw
  · refine ⟨(1-u)/2,(1-u)/2,u,by linarith,by linarith,hu,by ring,?_⟩
    apply Prod.ext <;> dsimp [x,m,segmentPoint,barycenter] <;>
      simp only [hp,hq] <;> ring

theorem overlap_of_same_side (t s : TriangleGeometry)
    (hp : s.p=t.p) (hq : s.q=t.q)
    (hs : 0<areaDet t.p t.q t.r*areaDet t.p t.q s.r) :
    ∃ x : Point, x∈t.interior ∧ x∈s.interior := by
  apply overlap_of_positive_weight t s hp hq
  dsimp [weightW]
  rcases lt_or_gt_of_ne t.nondegenerate with h|h
  · have hn : areaDet t.p t.q s.r<0 := by nlinarith
    exact div_pos_of_neg_of_neg hn h
  · have hn : 0<areaDet t.p t.q s.r := by nlinarith
    exact div_pos hn h

/-- Disjoint interiors with a common base must have their third vertices
on opposite strict sides of the supporting line. -/
theorem opposite_sides_of_disjoint (t s : TriangleGeometry)
    (hp : s.p=t.p) (hq : s.q=t.q)
    (hd : Disjoint t.interior s.interior) :
    areaDet t.p t.q t.r*areaDet t.p t.q s.r<0 := by
  have hs : areaDet t.p t.q s.r≠0 := by simpa only [hp,hq] using s.nondegenerate
  have hn := mul_ne_zero t.nondegenerate hs
  by_contra hh
  have hz : 0<areaDet t.p t.q t.r*areaDet t.p t.q s.r := by rcases lt_or_gt_of_ne hn with h|h <;> linarith
  obtain ⟨x,hxt,hxs⟩ := overlap_of_same_side t s hp hq hz
  exact Set.disjoint_left.mp hd hxt hxs

/-- Actual geometric capacity of one shared side. Triangles are allowed to
have arbitrary nondegenerate third vertices and arbitrary supporting lines. -/
theorem at_most_two {α : Type*} [Fintype α]
    (p q : Point) (t : α → TriangleGeometry)
    (hp : ∀ i, (t i).p=p) (hq : ∀ i, (t i).q=q)
    (hd : Pairwise (fun i j => Disjoint (t i).interior (t j).interior)) :
    Fintype.card α≤2 := by
  classical
  by_contra hh
  obtain ⟨a,b,c,hab,hac,hbc⟩ := Fintype.two_lt_card_iff.mp (by omega : 2<Fintype.card α)
  have h₁ := opposite_sides_of_disjoint (t a) (t b)
    ((hp b).trans (hp a).symm) ((hq b).trans (hq a).symm) (hd hab)
  have h₂ := opposite_sides_of_disjoint (t a) (t c)
    ((hp c).trans (hp a).symm) ((hq c).trans (hq a).symm) (hd hac)
  have h₃ := opposite_sides_of_disjoint (t b) (t c)
    ((hp c).trans (hp b).symm) ((hq c).trans (hq b).symm) (hd hbc)
  simp only [hp,hq] at h₁ h₂ h₃
  have hnonzero : areaDet p q (t a).r≠0 := by simpa only [hp,hq] using (t a).nondegenerate
  rcases lt_or_gt_of_ne hnonzero with h|h
  · have hb : 0<areaDet p q (t b).r := by nlinarith
    have hc : 0<areaDet p q (t c).r := by nlinarith
    have hpos := mul_pos hb hc
    linarith
  · have hb : areaDet p q (t b).r<0 := by nlinarith
    have hc : areaDet p q (t c).r<0 := by nlinarith
    have hpos := mul_pos_of_neg_of_neg hb hc
    linarith

#print axioms overlap_of_same_side
#print axioms opposite_sides_of_disjoint
#print axioms at_most_two
end Kobon.UpperEdgeCapacity

