import Kobon.UpperOpenMathAntipodalAdjacency

/-! Four outer core points determine an antipodal full star's center. -/
namespace Kobon.UpperOpenMathAntipodalCenterUniqueness
open Cells FanGeometry UpperFan UpperVertexBudget UpperTriangleIncidence
  UpperSharedIncidence UpperCoreExtraction UpperOpenMathAntipodalTwoCapChart Finset
set_option maxHeartbeats 1000000

def Between (d p q : Point) : Prop := ∃ u v : ℝ,
  0<u ∧ 0<v ∧ u+v=1 ∧ d=(u*p.1+v*q.1,u*p.2+v*q.2)

theorem Between.symm {d p q : Point} (h : Between d p q) : Between d q p := by
  obtain ⟨u,v,hu,hv,hadd,he⟩ := h
  exact ⟨v,u,hv,hu,by linarith,by rw [he]; congr 1 <;> ring⟩

theorem antipodal_between (c p q : Point) (t : ℝ) (ht : 0<t)
    (he : q=(c.1-t*(p.1-c.1),c.2-t*(p.2-c.2))) : Between c p q := by
  have hn : 1+t≠0 := by linarith
  refine ⟨t/(1+t),1/(1+t),by positivity,by positivity,?_,?_⟩
  · field_simp; ring
  · rw [he]
    apply Prod.ext <;> dsimp <;> field_simp <;> ring

theorem between_area (c p d a b : Point) (h : Between d a b) :
    ∃ u v : ℝ, 0<u ∧ 0<v ∧
      areaDet c p d=u*areaDet c p a+v*areaDet c p b := by
  obtain ⟨u,v,hu,hv,hs,he⟩ := h
  refine ⟨u,v,hu,hv,?_⟩
  rw [he]
  have hv : v=1-u := by linarith
  rw [hv]
  unfold areaDet
  dsimp
  ring

theorem two_area_zero (c p q d : Point) (hp : areaDet c p d=0)
    (hq : areaDet c q d=0) (hn : areaDet c p q≠0) : d=c := by
  apply Prod.ext
  · have h : areaDet c p q*(d.1-c.1)=0 := by
      calc
        _=(q.1-c.1)*areaDet c p d-(p.1-c.1)*areaDet c q d := by unfold areaDet; ring
        _=0 := by rw [hp,hq]; ring
    exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_left hn)
  · have h : areaDet c p q*(d.2-c.2)=0 := by
      calc
        _=(q.2-c.2)*areaDet c p d-(p.2-c.2)*areaDet c q d := by unfold areaDet; ring
        _=0 := by rw [hp,hq]; ring
    exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_left hn)

theorem quad_signs (c p q r s : Point) (pos : 0<areaDet c p q)
    (pr : Between c p r) (qs : Between c q s) :
    areaDet c q p<0 ∧ 0<areaDet c q r ∧ areaDet c q s=0 ∧ areaDet c p r=0 := by
  have qq : areaDet c q q=0 := by unfold areaDet; ring
  have pp : areaDet c p p=0 := by unfold areaDet; ring
  have ccq : areaDet c q c=0 := by unfold areaDet; ring
  have ccp : areaDet c p c=0 := by unfold areaDet; ring
  have pq : areaDet c q p= -areaDet c p q := by unfold areaDet; ring
  obtain ⟨u,v,hu,hv,hr⟩ := between_area c q c p r pr
  obtain ⟨u',v',hu',hv',hs⟩ := between_area c q c q s qs
  obtain ⟨u'',v'',hu'',hv'',hr0⟩ := between_area c p c p r pr
  refine ⟨by linarith,?_,?_,?_⟩
  · rw [ccq,pq] at hr
    nlinarith
  · rw [ccq,qq] at hs
    nlinarith
  · rw [ccp,pp] at hr0
    nlinarith

theorem diagonal_center (c d p q r s : Point) (pos : 0<areaDet c p q)
    (pr : Between c p r) (qs : Between c q s)
    (dpr : Between d p r) (dqs : Between d q s) : d=c := by
  obtain ⟨_,_,hs,hr⟩ := quad_signs c p q r s pos pr qs
  obtain ⟨u,v,hu,hv,hp⟩ := between_area c p d p r dpr
  obtain ⟨u',v',hu',hv',hq⟩ := between_area c q d q s dqs
  have pp : areaDet c p p=0 := by unfold areaDet; ring
  have qq : areaDet c q q=0 := by unfold areaDet; ring
  apply two_area_zero c p q d _ _ (ne_of_gt pos)
  · rw [hr,pp] at hp
    simpa using hp
  · rw [hs,qq] at hq
    simpa using hq

theorem opposite_edges_impossible (c d p q r s a b : Point)
    (neg : areaDet c q p<0) (pos : 0<areaDet c q r)
    (ha : areaDet c q a=0) (hb : areaDet c q b=0)
    (dpa : Between d p a) (drb : Between d r b) : False := by
  obtain ⟨u,v,hu,hv,h1⟩ := between_area c q d p a dpa
  obtain ⟨u',v',hu',hv',h2⟩ := between_area c q d r b drb
  rw [ha] at h1
  rw [hb] at h2
  nlinarith

theorem four_point_center_unique (c d p q r s a b e f : Point)
    (pos : 0<areaDet c p q) (pr : Between c p r) (qs : Between c q s)
    (dae : Between d a e) (dbf : Between d b f)
    (ma : a=p∨a=q∨a=r∨a=s) (mb : b=p∨b=q∨b=r∨b=s)
    (me : e=p∨e=q∨e=r∨e=s) (mf : f=p∨f=q∨f=r∨f=s)
    (ab : a≠b) (ae : a≠e) (af : a≠f) (be : b≠e) (bf : b≠f) (ef : e≠f) : d=c := by
  obtain ⟨neg,positive,szero,_⟩ := quad_signs c p q r s pos pr qs
  have qzero : areaDet c q q=0 := by unfold areaDet; ring
  rcases ma with ha|ha|ha|ha <;>
    rcases mb with hb|hb|hb|hb <;>
    rcases me with he|he|he|he <;>
    rcases mf with hf|hf|hf|hf
  all_goals simp only [ha,hb,he,hf] at dae dbf ab ae af be bf ef
  all_goals first
    | exact False.elim (ab rfl)
    | exact False.elim (ae rfl)
    | exact False.elim (af rfl)
    | exact False.elim (be rfl)
    | exact False.elim (bf rfl)
    | exact False.elim (ef rfl)
    | exact diagonal_center c d p q r s pos pr qs dae dbf
    | exact diagonal_center c d p q r s pos pr qs dae.symm dbf
    | exact diagonal_center c d p q r s pos pr qs dae dbf.symm
    | exact diagonal_center c d p q r s pos pr qs dae.symm dbf.symm
    | exact diagonal_center c d p q r s pos pr qs dbf dae
    | exact diagonal_center c d p q r s pos pr qs dbf.symm dae
    | exact diagonal_center c d p q r s pos pr qs dbf dae.symm
    | exact diagonal_center c d p q r s pos pr qs dbf.symm dae.symm
    | exact False.elim (opposite_edges_impossible c d p q r s q s neg positive qzero szero dae dbf)
    | exact False.elim (opposite_edges_impossible c d p q r s q s neg positive qzero szero dae.symm dbf)
    | exact False.elim (opposite_edges_impossible c d p q r s q s neg positive qzero szero dae dbf.symm)
    | exact False.elim (opposite_edges_impossible c d p q r s q s neg positive qzero szero dae.symm dbf.symm)
    | exact False.elim (opposite_edges_impossible c d p q r s q s neg positive qzero szero dbf dae)
    | exact False.elim (opposite_edges_impossible c d p q r s q s neg positive qzero szero dbf.symm dae)
    | exact False.elim (opposite_edges_impossible c d p q r s q s neg positive qzero szero dbf dae.symm)
    | exact False.elim (opposite_edges_impossible c d p q r s q s neg positive qzero szero dbf.symm dae.symm)
    | exact False.elim (opposite_edges_impossible c d p q r s s q neg positive szero qzero dae dbf)
    | exact False.elim (opposite_edges_impossible c d p q r s s q neg positive szero qzero dae.symm dbf)
    | exact False.elim (opposite_edges_impossible c d p q r s s q neg positive szero qzero dae dbf.symm)
    | exact False.elim (opposite_edges_impossible c d p q r s s q neg positive szero qzero dae.symm dbf.symm)
    | exact False.elim (opposite_edges_impossible c d p q r s s q neg positive szero qzero dbf dae)
    | exact False.elim (opposite_edges_impossible c d p q r s s q neg positive szero qzero dbf.symm dae)
    | exact False.elim (opposite_edges_impossible c d p q r s s q neg positive szero qzero dbf dae.symm)
    | exact False.elim (opposite_edges_impossible c d p q r s s q neg positive szero qzero dbf.symm dae.symm)

theorem antipodal_outer_between {n : ℕ} {L : ℕ → Line ℝ}
    (f : Sectors n 3 L) (z : ZMod 6) : Between f.center (f.point z) (f.point (z+3)) := by
  obtain ⟨t,ht,he⟩ := f.antipodal z
  exact antipodal_between f.center (f.point z) (f.point (z+3)) t ht he

#print axioms four_point_center_unique
end Kobon.UpperOpenMathAntipodalCenterUniqueness
