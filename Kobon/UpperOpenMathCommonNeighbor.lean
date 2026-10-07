import Kobon.UpperOpenMathVertexBlocks

/-! Two used elementary edges on one line force their common endpoint to
lie between their other endpoints. An intervening arrangement vertex rules
out every different common endpoint. -/
namespace Kobon.UpperOpenMathCommonNeighbor
open Cells UpperVertexBudget UpperEdgeInventory UpperTriangleIncidence
  UpperOpenMathVertexBlocks Finset
set_option maxHeartbeats 1000000

theorem coordinate_between (l : Line ℝ) (valid : l.a≠0 ∨ l.b≠0)
    (p q v : Point) (hp : affineEval l p=0) (hq : affineEval l q=0)
    (hv : affineEval l v=0) (left : coordinate l p<coordinate l v)
    (right : coordinate l v<coordinate l q) :
    ∃ t : ℝ, 0<t ∧ t<1 ∧ v=segmentPoint p q t := by
  let u := (coordinate l v-coordinate l p)/(coordinate l q-coordinate l p)
  have den : 0<coordinate l q-coordinate l p := by linarith
  have hu : 0<u := div_pos (by linarith) den
  have hu1 : u<1 := (div_lt_one den).mpr (by linarith)
  have eq : (1-u)*coordinate l p+u*coordinate l q=coordinate l v := by
    dsimp [u]
    field_simp
    ring
  refine ⟨u,hu,hu1,?_⟩
  rw [← parameter_coordinate l valid v hv,← parameter_coordinate l valid p hp,
    ← parameter_coordinate l valid q hq,← parameter_segment,eq]

theorem coordinate_ne_of_ne (l : Line ℝ) (valid : l.a≠0 ∨ l.b≠0)
    (p q : Point) (hp : affineEval l p=0) (hq : affineEval l q=0) (ne : p≠q) :
    coordinate l p≠coordinate l q := by
  intro eq
  apply ne
  rw [← parameter_coordinate l valid p hp,← parameter_coordinate l valid q hq,eq]

theorem coordinate_segment (l : Line ℝ) (p q : Point) (u : ℝ) :
    coordinate l (segmentPoint p q u)=(1-u)*coordinate l p+u*coordinate l q := by
  unfold coordinate
  split_ifs <;> rfl

theorem between_swap (p q v : Point)
    (h : ∃ t : ℝ, 0<t ∧ t<1 ∧ v=segmentPoint p q t) :
    ∃ t : ℝ, 0<t ∧ t<1 ∧ v=segmentPoint q p t := by
  obtain ⟨t,ht0,ht1,hv⟩ := h
  refine ⟨1-t,by linarith,by linarith,?_⟩
  rw [hv]
  apply Prod.ext <;> dsimp [segmentPoint] <;> ring

theorem certificate_common_used_center_between {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (ht : ∀ a, TrianglePredicate n L (tri a))
    (i : Fin n) (c p q : Point)
    (hc : affineEval (L i) c=0) (hp : affineEval (L i) p=0)
    (hq : affineEval (L i) q=0) (vp : p∈vertices n L) (vq : q∈vertices n L)
    (pq : p≠q)
    (cp : {c,p}∈usedEdges (fun a => ofPredicate n L (tri a) hL (ht a)))
    (cq : {c,q}∈usedEdges (fun a => ofPredicate n L (tri a) hL (ht a))) :
    ∃ t : ℝ, 0<t ∧ t<1 ∧ c=segmentPoint p q t := by
  have valid := line_valid n L hL hn i
  obtain ⟨j,ecp⟩ := certificate_used_pair_elementary n L hL tri ht c p cp
  obtain ⟨k,ecq⟩ := certificate_used_pair_elementary n L hL tri ht c q cq
  have cpn := coordinate_ne_of_ne (L i) valid c p hc hp ecp.1
  have cqn := coordinate_ne_of_ne (L i) valid c q hc hq ecq.1
  have pqn := coordinate_ne_of_ne (L i) valid p q hp hq pq
  rcases lt_or_gt_of_ne pqn with order|order
  · by_cases left : coordinate (L i) p<coordinate (L i) c
    · by_cases right : coordinate (L i) c<coordinate (L i) q
      · exact coordinate_between (L i) valid p q c hp hq hc left right
      · have mid : coordinate (L i) q<coordinate (L i) c := by rcases lt_or_gt_of_ne cqn with h|h; exact False.elim (right h); exact h
        exact False.elim ((certificate_vertex_blocks_used_edge n L hL tri ht c p q vq
          (between_swap p c q (coordinate_between (L i) valid p c q hp hc hq order mid))) cp)
    · have mid : coordinate (L i) c<coordinate (L i) p := by rcases lt_or_gt_of_ne cpn with h|h; exact h; exact False.elim (left h)
      exact False.elim ((certificate_vertex_blocks_used_edge n L hL tri ht c q p vp
        (coordinate_between (L i) valid c q p hc hq hp mid order)) cq)
  · by_cases left : coordinate (L i) q<coordinate (L i) c
    · by_cases right : coordinate (L i) c<coordinate (L i) p
      · exact between_swap q p c (coordinate_between (L i) valid q p c hq hp hc left right)
      · have mid : coordinate (L i) p<coordinate (L i) c := by rcases lt_or_gt_of_ne cpn with h|h; exact False.elim (right h); exact h
        exact False.elim ((certificate_vertex_blocks_used_edge n L hL tri ht c q p vp
          (between_swap q c p (coordinate_between (L i) valid q c p hq hc hp order mid))) cq)
    · have mid : coordinate (L i) c<coordinate (L i) q := by rcases lt_or_gt_of_ne cqn with h|h; exact h; exact False.elim (left h)
      exact False.elim ((certificate_vertex_blocks_used_edge n L hL tri ht c p q vq
        (coordinate_between (L i) valid c p q hc hp hq mid order)) cp)

theorem certificate_intervening_vertex_no_common_used_neighbor {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (ht : ∀ a, TrianglePredicate n L (tri a))
    (i : Fin n) (c p q v : Point)
    (hc : affineEval (L i) c=0) (hp : affineEval (L i) p=0)
    (hq : affineEval (L i) q=0) (vp : p∈vertices n L) (vq : q∈vertices n L)
    (vv : v∈vertices n L) (pq : p≠q) (vc : v≠c)
    (between : ∃ t : ℝ, 0<t ∧ t<1 ∧ v=segmentPoint p q t) :
    ¬({c,p}∈usedEdges (fun a => ofPredicate n L (tri a) hL (ht a)) ∧
      {c,q}∈usedEdges (fun a => ofPredicate n L (tri a) hL (ht a))) := by
  intro ⟨cp,cq⟩
  have valid := line_valid n L hL hn i
  have center := certificate_common_used_center_between n L hL hn tri ht i c p q hc hp hq vp vq pq cp cq
  obtain ⟨t,ht0,ht1,veq⟩ := between
  have hv : affineEval (L i) v=0 := by rw [veq,affineEval_segment,hp,hq]; ring
  have vcn := coordinate_ne_of_ne (L i) valid v c hv hc vc
  have vcoord : coordinate (L i) v=(1-t)*coordinate (L i) p+t*coordinate (L i) q := by
    rw [veq,coordinate_segment]
  have pqn := coordinate_ne_of_ne (L i) valid p q hp hq pq
  rcases lt_or_gt_of_ne pqn with order|order
  · have left : coordinate (L i) p<coordinate (L i) v := by nlinarith
    have right : coordinate (L i) v<coordinate (L i) q := by nlinarith
    rcases lt_or_gt_of_ne vcn with less|more
    · exact (certificate_vertex_blocks_used_edge n L hL tri ht c p v vv
        (between_swap p c v (coordinate_between (L i) valid p c v hp hc hv left less))) cp
    · exact (certificate_vertex_blocks_used_edge n L hL tri ht c q v vv
        (coordinate_between (L i) valid c q v hc hq hv more right)) cq
  · have left : coordinate (L i) q<coordinate (L i) v := by nlinarith
    have right : coordinate (L i) v<coordinate (L i) p := by nlinarith
    rcases lt_or_gt_of_ne vcn with less|more
    · exact (certificate_vertex_blocks_used_edge n L hL tri ht c q v vv
        (between_swap q c v (coordinate_between (L i) valid q c v hq hc hv left less))) cq
    · exact (certificate_vertex_blocks_used_edge n L hL tri ht c p v vv
        (coordinate_between (L i) valid c p v hc hp hv more right)) cp

theorem certificate_collinear_used_triangle_impossible {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (ht : ∀ a, TrianglePredicate n L (tri a))
    (i : Fin n) (c p q : Point)
    (hc : affineEval (L i) c=0) (hp : affineEval (L i) p=0)
    (hq : affineEval (L i) q=0) (vc : c∈vertices n L)
    (vp : p∈vertices n L) (vq : q∈vertices n L) (pq : p≠q)
    (cp : {c,p}∈usedEdges (fun a => ofPredicate n L (tri a) hL (ht a)))
    (cq : {c,q}∈usedEdges (fun a => ofPredicate n L (tri a) hL (ht a)))
    (edge : {p,q}∈usedEdges (fun a => ofPredicate n L (tri a) hL (ht a))) : False := by
  have between := certificate_common_used_center_between n L hL hn tri ht i c p q
    hc hp hq vp vq pq cp cq
  exact certificate_vertex_blocks_used_edge n L hL tri ht p q c vc between edge

#print axioms certificate_common_used_center_between
#print axioms certificate_intervening_vertex_no_common_used_neighbor
#print axioms certificate_collinear_used_triangle_impossible
end Kobon.UpperOpenMathCommonNeighbor
