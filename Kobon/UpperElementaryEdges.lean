import Kobon.Cells

/-!
# Certified triangle sides are elementary arrangement segments

The geometric certificate's weak-side condition implies that an arrangement
line meeting the relative interior of a triangle side contains that entire
side. Under pairwise nonparallelness it must be the side's supporting line.
Thus no other arrangement vertex lies in a certified side's relative interior.
-/
namespace Kobon.UpperElementaryEdges
open Cells

/-- A zero at a strict convex combination of two same-sign values forces
both values to vanish. -/
theorem endpoints_zero_of_segment_zero (l : Line ℝ) (p q : Point)
    (same_side : (0≤affineEval l p ∧ 0≤affineEval l q) ∨
      (affineEval l p≤0 ∧ affineEval l q≤0))
    (u : ℝ) (hu : 0<u) (hu1 : u<1)
    (hz : affineEval l (segmentPoint p q u)=0) :
    affineEval l p=0 ∧ affineEval l q=0 := by
  rw [affineEval_segment] at hz
  have hu' : 0<1-u := by linarith
  rcases same_side with ⟨hp,hq⟩|⟨hp,hq⟩
  · have ha := mul_nonneg hu'.le hp
    have hb := mul_nonneg hu.le hq
    have hap : (1-u)*affineEval l p=0 := by linarith
    have hbp : u*affineEval l q=0 := by linarith
    exact ⟨(mul_eq_zero.mp hap).resolve_left hu'.ne',
      (mul_eq_zero.mp hbp).resolve_left hu.ne'⟩
  · have ha := mul_nonpos_of_nonneg_of_nonpos hu'.le hp
    have hb := mul_nonpos_of_nonneg_of_nonpos hu.le hq
    have hap : (1-u)*affineEval l p=0 := by linarith
    have hbp : u*affineEval l q=0 := by linarith
    exact ⟨(mul_eq_zero.mp hap).resolve_left hu'.ne',
      (mul_eq_zero.mp hbp).resolve_left hu.ne'⟩

/-- An elementary side interface, expressed directly by affine coordinates. -/
def Elementary (n : ℕ) (L : ℕ → Line ℝ) (edge : Fin n) (p q : Point) : Prop :=
  p≠q ∧ affineEval (L edge) p=0 ∧ affineEval (L edge) q=0 ∧
    ∀ j : Fin n, j≠edge → ∀ u : ℝ, 0<u → u<1 →
      affineEval (L j) (segmentPoint p q u)≠0

theorem Elementary.symm {n : ℕ} {L : ℕ → Line ℝ} {edge : Fin n} {p q : Point}
    (he : Elementary n L edge p q) : Elementary n L edge q p := by
  refine ⟨he.1.symm,he.2.2.1,he.2.1,?_⟩
  intro j hj u hu hu1
  have hs : segmentPoint q p u=segmentPoint p q (1-u) := by
    apply Prod.ext <;> dsimp [segmentPoint] <;> ring
  rw [hs]
  exact he.2.2.2 j hj (1-u) (by linarith) (by linarith)

theorem elementary_of_same_side (n : ℕ) (L : ℕ → Line ℝ)
    (hL : NoParallel n L) (edge : Fin n) (p q : Point) (hpq : p≠q)
    (hp : affineEval (L edge) p=0) (hq : affineEval (L edge) q=0)
    (side : ∀ j : Fin n, (0≤affineEval (L j) p ∧ 0≤affineEval (L j) q) ∨
      (affineEval (L j) p≤0 ∧ affineEval (L j) q≤0)) :
    Elementary n L edge p q := by
  refine ⟨hpq,hp,hq,?_⟩
  intro j hje u hu hu1 hz
  obtain ⟨hjp,hjq⟩ := endpoints_zero_of_segment_zero (L j) p q (side j) u hu hu1 hz
  apply hpq
  exact two_lines_two_points (L edge) (L j) p q
    (noParallel_any n L hL edge j edge.isLt j.isLt
      (fun h => hje (Fin.ext h.symm))) hp hq hjp hjq

/-- Every first side of every real triangle satisfying the repository's
certificate predicate is an elementary segment of the full arrangement. -/
theorem predicate_side_elementary (n : ℕ) (L : ℕ → Line ℝ) (t : Triple)
    (hL : NoParallel n L) (ht : TrianglePredicate n L t) :
    Elementary n L ⟨t.i,by have := ht.1; have := ht.2.1; have := ht.2.2.1; omega⟩
      (ofPredicate n L t hL ht).p (ofPredicate n L t hL ht).q := by
  let f := ofPredicate n L t hL ht
  apply elementary_of_same_side n L hL
    ⟨t.i,by have := ht.1; have := ht.2.1; have := ht.2.2.1; omega⟩ f.p f.q
    (nondegenerate_pair_ne f.p f.q f.r f.nondegenerate) f.Cp f.Cq
  intro j
  rcases weakSide_of_predicate n L t hL ht j with h|h
  · exact Or.inl ⟨h.1,h.2.1⟩
  · exact Or.inr ⟨h.1,h.2.1⟩

/-- All three certified triangle sides satisfy the elementary-edge interface. -/
theorem predicate_all_sides_elementary (n : ℕ) (L : ℕ → Line ℝ) (t : Triple)
    (hL : NoParallel n L) (ht : TrianglePredicate n L t) :
    let f := ofPredicate n L t hL ht
    Elementary n L ⟨t.i,by have := ht.1; have := ht.2.1; have := ht.2.2.1; omega⟩ f.p f.q ∧
    Elementary n L ⟨t.j,by have := ht.2.1; have := ht.2.2.1; omega⟩ f.p f.r ∧
    Elementary n L ⟨t.k,ht.2.2.1⟩ f.q f.r := by
  let f := ofPredicate n L t hL ht
  refine ⟨predicate_side_elementary n L t hL ht,?_,?_⟩
  · have hpr : f.p≠f.r := by
      intro he
      exact f.Ap (he ▸ f.Ar)
    apply elementary_of_same_side n L hL
      ⟨t.j,by have := ht.2.1; have := ht.2.2.1; omega⟩ f.p f.r hpr f.Bp f.Br
    intro j
    rcases weakSide_of_predicate n L t hL ht j with h|h
    · exact Or.inl ⟨h.1,h.2.2⟩
    · exact Or.inr ⟨h.1,h.2.2⟩
  · have hqr : f.q≠f.r := by
      intro he
      exact f.Bq (he ▸ f.Br)
    apply elementary_of_same_side n L hL ⟨t.k,ht.2.2.1⟩ f.q f.r hqr f.Aq f.Ar
    intro j
    rcases weakSide_of_predicate n L t hL ht j with h|h
    · exact Or.inl ⟨h.2.1,h.2.2⟩
    · exact Or.inr ⟨h.2.1,h.2.2⟩

/-- Two different arrangement lines cannot meet in an elementary side's
relative interior. This extracts the absence of intermediate vertices. -/
theorem no_vertex_in_relative_interior {n : ℕ} {L : ℕ → Line ℝ}
    {edge : Fin n} {p q : Point} (he : Elementary n L edge p q)
    (a b : Fin n) (hab : a≠b) (u : ℝ) (hu : 0<u) (hu1 : u<1)
    (ha : affineEval (L a) (segmentPoint p q u)=0)
    (hb : affineEval (L b) (segmentPoint p q u)=0) : False := by
  by_cases hae : a=edge
  · exact he.2.2.2 b (fun h => hab (hae.trans h.symm)) u hu hu1 hb
  · exact he.2.2.2 a hae u hu hu1 ha

#print axioms predicate_side_elementary
#print axioms predicate_all_sides_elementary
#print axioms no_vertex_in_relative_interior
end Kobon.UpperElementaryEdges

