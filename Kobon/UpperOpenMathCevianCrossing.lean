import Kobon.UpperOpenMathAntipodalCenterUniqueness
import Kobon.UpperOpenMathCommonNeighbor

/-! Strict triangle cevians and actual elementary-side obstructions. -/
namespace Kobon.UpperOpenMathCevianCrossing
open Cells UpperVertexBudget UpperTriangleIncidence UpperEdgeInventory
  UpperOpenMathVertexBlocks UpperOpenMathCommonNeighbor
  UpperOpenMathAntipodalCenterUniqueness Finset
set_option maxHeartbeats 1000000

theorem Between.segment {c p q : Point} (h : Between c p q) :
    ∃ t : ℝ, 0<t ∧ t<1 ∧ c=segmentPoint p q t := by
  obtain ⟨u,v,hu,hv,hadd,he⟩ := h
  refine ⟨v,hv,by linarith,?_⟩
  have heq : u=1-v := by linarith
  simpa only [heq,segmentPoint] using he

theorem cevians_strictly_cross (p q r c d : Point)
    (cpq : Between c p q) (dpr : Between d p r) :
    ∃ z : Point, ∃ t u : ℝ, 0<t ∧ t<1 ∧ 0<u ∧ u<1 ∧
      z=segmentPoint c r t ∧ z=segmentPoint d q u := by
  obtain ⟨t,ht0,ht1,ceq⟩ := Between.segment cpq
  obtain ⟨u,hu0,hu1,deq⟩ := Between.segment dpr
  have hut : u*t<1 := lt_trans (by nlinarith : u*t<u) hu1
  have den : 0<1-u*t := by linarith
  let v := u*(1-t)/(1-u*t)
  let w := t*(1-u)/(1-u*t)
  have v0 : 0<v := div_pos (mul_pos hu0 (by linarith)) den
  have v1 : v<1 := (div_lt_one den).mpr (by nlinarith)
  have w0 : 0<w := div_pos (mul_pos ht0 (by linarith)) den
  have w1 : w<1 := (div_lt_one den).mpr (by nlinarith)
  refine ⟨segmentPoint c r v,v,w,v0,v1,w0,w1,rfl,?_⟩
  rw [ceq,deq]
  apply Prod.ext <;> dsimp [segmentPoint,v,w] <;> field_simp [den.ne'] <;> ring

theorem certificate_cevian_edges_impossible {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (ht : ∀ a, TrianglePredicate n L (tri a))
    (p q r c d : Point) (nondeg : areaDet p q r≠0)
    (cpq : Between c p q) (dpr : Between d p r)
    (cr : {c,r}∈usedEdges (fun a => ofPredicate n L (tri a) hL (ht a)))
    (dq : {d,q}∈usedEdges (fun a => ofPredicate n L (tri a) hL (ht a))) : False := by
  obtain ⟨i,ei⟩ := certificate_used_pair_elementary n L hL tri ht c r cr
  obtain ⟨j,ej⟩ := certificate_used_pair_elementary n L hL tri ht d q dq
  obtain ⟨t,ht0,ht1,ceq⟩ := Between.segment cpq
  have cq : areaDet c q r=(1-t)*areaDet p q r := by rw [ceq]; dsimp [areaDet,segmentPoint]; ring
  have cqne : areaDet c q r≠0 := by rw [cq]; exact mul_ne_zero (ne_of_gt (by linarith)) nondeg
  have ji : j≠i := by
    intro equal
    have qj := ej.2.2.1
    rw [equal] at qj
    obtain ⟨ha,hb⟩ := three_zeros_force_zero_normal (L i) c q r cqne ei.2.1 qj ei.2.2.1
    rcases line_valid n L hL hn i with h|h
    · exact h ha
    · exact h hb
  obtain ⟨z,v,w,v0,v1,w0,w1,zc,zd⟩ := cevians_strictly_cross p q r c d cpq dpr
  have onj : affineEval (L j) (segmentPoint c r v)=0 := by
    rw [←zc,zd,affineEval_segment,ej.2.1,ej.2.2.1]
    ring
  exact ei.2.2.2 j ji v v0 v1 onj

theorem certificate_same_pair_centers_unique {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (ht : ∀ a, TrianglePredicate n L (tri a))
    (p q c d : Point) (vp : p∈vertices n L) (vq : q∈vertices n L)
    (vd : d∈vertices n L) (pq : p≠q)
    (cpq : Between c p q) (dpq : Between d p q)
    (cp : {c,p}∈usedEdges (fun a => ofPredicate n L (tri a) hL (ht a)))
    (cq : {c,q}∈usedEdges (fun a => ofPredicate n L (tri a) hL (ht a))) : c=d := by
  by_contra ne
  obtain ⟨i,ei⟩ := certificate_used_pair_elementary n L hL tri ht c p cp
  obtain ⟨t,ht0,ht1,ceq⟩ := Between.segment cpq
  have qline : affineEval (L i) q=0 := by
    have h := ei.2.1
    rw [ceq,affineEval_segment,ei.2.2.1] at h
    have hz : t*affineEval (L i) q=0 := by simpa using h
    exact (mul_eq_zero.mp hz).resolve_left ht0.ne'
  exact (certificate_intervening_vertex_no_common_used_neighbor n L hL hn tri ht
    i c p q d ei.2.1 ei.2.2.1 qline vp vq vd pq (fun equal=>ne equal.symm)
      (Between.segment dpq)) ⟨cp,cq⟩

theorem certificate_boundary_pair_centers_unique {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (ht : ∀ a, TrianglePredicate n L (tri a))
    (p q r c d : Point) (nondeg : areaDet p q r≠0)
    (vp : p∈vertices n L) (vq : q∈vertices n L) (vr : r∈vertices n L)
    (vc : c∈vertices n L) (vd : d∈vertices n L)
    (cside : Between c p q∨Between c p r∨Between c q r)
    (dside : Between d p q∨Between d p r∨Between d q r)
    (cp : {c,p}∈usedEdges (fun a => ofPredicate n L (tri a) hL (ht a)))
    (cq : {c,q}∈usedEdges (fun a => ofPredicate n L (tri a) hL (ht a)))
    (cr : {c,r}∈usedEdges (fun a => ofPredicate n L (tri a) hL (ht a)))
    (dp : {d,p}∈usedEdges (fun a => ofPredicate n L (tri a) hL (ht a)))
    (dq : {d,q}∈usedEdges (fun a => ofPredicate n L (tri a) hL (ht a)))
    (dr : {d,r}∈usedEdges (fun a => ofPredicate n L (tri a) hL (ht a))) : c=d := by
  have pq : p≠q := nondegenerate_pair_ne p q r nondeg
  have pr : p≠r := by intro he; apply nondeg; rw [he]; unfold areaDet; ring
  have qr : q≠r := by intro he; apply nondeg; rw [he]; unfold areaDet; ring
  have qpr : areaDet q p r≠0 := by
    have eq : areaDet q p r= -areaDet p q r := by unfold areaDet; ring
    rw [eq]
    exact neg_ne_zero.mpr nondeg
  have rpq : areaDet r p q≠0 := by
    have eq : areaDet r p q=areaDet p q r := by unfold areaDet; ring
    rw [eq]; exact nondeg
  rcases cside with cpq|cpr|cqr <;> rcases dside with dpq|dpr|dqr
  · exact certificate_same_pair_centers_unique n L hL hn tri ht p q c d vp vq vd pq cpq dpq cp cq
  · exact False.elim (certificate_cevian_edges_impossible n L hL hn tri ht p q r c d nondeg cpq dpr cr dq)
  · exact False.elim (certificate_cevian_edges_impossible n L hL hn tri ht q p r c d qpr cpq.symm dqr cr dp)
  · exact False.elim (certificate_cevian_edges_impossible n L hL hn tri ht p q r d c nondeg dpq cpr dr cq)
  · exact certificate_same_pair_centers_unique n L hL hn tri ht p r c d vp vr vd pr cpr dpr cp cr
  · exact False.elim (certificate_cevian_edges_impossible n L hL hn tri ht r p q c d rpq cpr.symm dqr.symm cq dp)
  · exact False.elim (certificate_cevian_edges_impossible n L hL hn tri ht q p r d c qpr dpq.symm cqr dr cp)
  · exact False.elim (certificate_cevian_edges_impossible n L hL hn tri ht r p q d c rpq dpr.symm cqr.symm dq cp)
  · exact certificate_same_pair_centers_unique n L hL hn tri ht q r c d vq vr vd qr cqr dqr cq cr

#print axioms certificate_boundary_pair_centers_unique
end Kobon.UpperOpenMathCevianCrossing
