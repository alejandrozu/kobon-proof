import Kobon.UpperEdgeInventory
import Kobon.UpperElementaryEdges
import Kobon.UpperFanSupport

/-! Explicit between-point geometry and actual vertex obstructions to a
certified edge. These lemmas concern real coordinates, not a graph oracle. -/
namespace Kobon.UpperOpenMathVertexBlocks
open Cells FanGeometry UpperVertexBudget UpperTriangleIncidence UpperElementaryEdges Finset
set_option maxHeartbeats 1000000

theorem oriented_collinear_between (c v p u : Point)
    (left : 0<areaDet c v p) (right : 0<areaDet c p u)
    (collinear : areaDet v p u=0) :
    ∃ t : ℝ, 0<t ∧ t<1 ∧ p=segmentPoint v u t := by
  let A := areaDet c v p
  let B := areaDet c p u
  have hA : 0<A := left
  have hB : 0<B := right
  have hden : 0<A+B := add_pos hA hB
  have hx : (A+B)*p.1=B*v.1+A*u.1 := by
    have identity : (A+B)*p.1-B*v.1-A*u.1=areaDet v p u*(p.1-c.1) := by dsimp [A,B,areaDet]; ring
    rw [collinear,zero_mul] at identity
    linarith
  have hy : (A+B)*p.2=B*v.2+A*u.2 := by
    have identity : (A+B)*p.2-B*v.2-A*u.2=areaDet v p u*(p.2-c.2) := by dsimp [A,B,areaDet]; ring
    rw [collinear,zero_mul] at identity
    linarith
  refine ⟨A/(A+B),div_pos hA hden,(div_lt_one hden).mpr (by linarith),?_⟩
  apply Prod.ext
  · dsimp [segmentPoint]
    field_simp [hden.ne']
    nlinarith
  · dsimp [segmentPoint]
    field_simp [hden.ne']
    nlinarith

theorem antipodal_center_between (c p q : Point) (s : ℝ) (hs : 0<s)
    (anti : q=(c.1-s*(p.1-c.1),c.2-s*(p.2-c.2))) :
    ∃ t : ℝ, 0<t ∧ t<1 ∧ c=segmentPoint p q t := by
  have hd : 0<1+s := by linarith
  refine ⟨1/(1+s),div_pos (by norm_num) hd,(div_lt_one hd).mpr (by linarith),?_⟩
  rw [anti]
  apply Prod.ext <;> dsimp [segmentPoint] <;> field_simp <;> ring

theorem ordinary_cap_between {n r : ℕ} [NeZero (2*r)] {L : ℕ → Line ℝ}
    (f : UpperFan.Sectors n r L) (full : f.triangular=univ)
    (positive : ∀ z, 0<areaDet f.center (f.point z) (f.point (z+1)))
    (z : ZMod (2*r)) (ord : OrdinaryAt n L (f.point z)) :
    ∃ t : ℝ, 0<t ∧ t<1 ∧ f.point z=segmentPoint (f.point (z-1)) (f.point (z+1)) t :=
  oriented_collinear_between f.center (f.point (z-1)) (f.point z) (f.point (z+1))
    (by simpa using positive (z-1)) (positive z)
    (UpperFanSupport.Sectors.collinear_at_ordinary f full z ord)

theorem predicate_side_elementary_exists (n : ℕ) (L : ℕ → Line ℝ)
    (hL : NoParallel n L) (t : Triple) (ht : TrianglePredicate n L t) (side : Fin 3) :
    ∃ i : Fin n, Elementary n L i (sideTriangle (ofPredicate n L t hL ht) side).p
      (sideTriangle (ofPredicate n L t hL ht) side).q := by
  have all := predicate_all_sides_elementary n L t hL ht
  fin_cases side
  · exact ⟨_,all.1⟩
  · exact ⟨_,all.2.2⟩
  · exact ⟨_,all.2.1.symm⟩

theorem certificate_used_pair_elementary {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L)
    (tri : α → Triple) (ht : ∀ a, TrianglePredicate n L (tri a))
    (p q : Point) (used : {p,q}∈usedEdges (fun a => ofPredicate n L (tri a) hL (ht a))) :
    ∃ i : Fin n, Elementary n L i p q := by
  classical
  obtain ⟨a,_,pair⟩ := mem_image.mp used
  let s := sideTriangle (ofPredicate n L (tri a.1) hL (ht a.1)) a.2
  have eqPair : ({s.p,s.q} : Edge)={p,q} := pair
  have sp : s.p=p ∨ s.p=q := by
    have hm : s.p∈({p,q} : Edge) := by rw [← eqPair]; simp
    simpa only [mem_insert,mem_singleton] using hm
  have sq : s.q=p ∨ s.q=q := by
    have hm : s.q∈({p,q} : Edge) := by rw [← eqPair]; simp
    simpa only [mem_insert,mem_singleton] using hm
  obtain ⟨i,elementary⟩ := predicate_side_elementary_exists n L hL (tri a.1) (ht a.1) a.2
  change Elementary n L i s.p s.q at elementary
  rcases sp with sp|sp <;> rcases sq with sq|sq
  · exact False.elim (elementary.1 (sp.trans sq.symm))
  · exact ⟨i,by simpa only [sp,sq] using elementary⟩
  · exact ⟨i,by simpa only [sp,sq] using elementary.symm⟩
  · exact False.elim (elementary.1 (sp.trans sq.symm))

theorem certificate_vertex_blocks_used_edge {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L)
    (tri : α → Triple) (ht : ∀ a, TrianglePredicate n L (tri a))
    (p q v : Point) (hv : v∈vertices n L)
    (between : ∃ t : ℝ, 0<t ∧ t<1 ∧ v=segmentPoint p q t) :
    {p,q}∉usedEdges (fun a => ofPredicate n L (tri a) hL (ht a)) := by
  classical
  intro used
  obtain ⟨edge,elementary⟩ := certificate_used_pair_elementary n L hL tri ht p q used
  obtain ⟨ij,hij,hpoint⟩ := mem_image.mp hv
  have ne := (mem_offDiag.mp hij).2.2
  have on := (intersection_eq_iff n L hL ij.1 ij.2 ne v).mp hpoint
  obtain ⟨t,ht0,ht1,he⟩ := between
  rw [he] at on
  exact no_vertex_in_relative_interior elementary ij.1 ij.2 ne t ht0 ht1 on.1 on.2

#print axioms oriented_collinear_between
#print axioms ordinary_cap_between
#print axioms certificate_vertex_blocks_used_edge
end Kobon.UpperOpenMathVertexBlocks
