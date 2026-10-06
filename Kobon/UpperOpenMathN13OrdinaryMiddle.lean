import Kobon.UpperOpenMathAntipodalFullNeighborPair

/-! Two full antipodal stars opposite an ordinary intermediate tip cannot
both close through a common outer triple. The actual identification of that
outer endpoint is a separate nearest-used-side extraction. -/
namespace Kobon.UpperOpenMathN13OrdinaryMiddle
open Cells FanGeometry UpperFan UpperVertexBudget UpperCoreExtraction
  UpperOpenMathAntipodalTwoCapChart UpperOpenMathAntipodalAdjacency
  UpperOpenMathAntipodalFullNeighborPair UpperOpenMathVertexBlocks Finset
set_option maxHeartbeats 1000000

theorem ordinary_middle_pair_impossible {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (G : α → TriangleGeometry)
    (a b : Sectors n 3 L) (ad : AntipodalData G a) (bd : AntipodalData G b)
    (c U R : Point) (w x : ZMod 6)
    (ac : a.point w=c) (bc : b.point x=c)
    (aU : a.point (w-1)=U) (bU : b.point (x+1)=U)
    (aR : a.point (w-2)=R) (bR : b.point (x+2)=R)
    (ordU : OrdinaryAt n L U) (rc : (supports n L c).card=3)
    (rr : (supports n L R).card=3) (axis : Fin n)
    (axisA : affineEval (L axis) a.center=0)
    (axisB : affineEval (L axis) b.center=0)
    (axisU : affineEval (L axis) U=0) (axisC : affineEval (L axis) c≠0)
    (ab : a.center≠b.center) : False := by
  classical
  let ca := a.radial w
  let cb := b.radial x
  let cu := a.opposite (w-1)
  let ar := a.radial (w-2)
  let br := b.radial (x+2)
  have wprev : w-1-1=w-2 := by ring
  have wnext : (w-2)+1=w-1 := by ring
  have xnext : (x+1)+1=x+2 := by ring
  have hOrdA : OrdinaryAt n L (a.point (w-1)) := by rw [aU]; exact ordU
  have hOrdB : OrdinaryAt n L (b.point (x+1)) := by rw [bU]; exact ordU
  have aCaps : a.opposite (w-2)=cu := by
    simpa only [wprev] using cap_eq_at_ordinary a ad.triangular_eq (w-1) hOrdA
  have caC : affineEval (L ca) c=0 := by rw [←ac]; exact a.radial_point w
  have cbC : affineEval (L cb) c=0 := by rw [←bc]; exact b.radial_point x
  have cuC : affineEval (L cu) c=0 := by
    rw [←ac]
    simpa only [sub_add_cancel] using cap_right a ad.triangular_eq (w-1)
  have cuU : affineEval (L cu) U=0 := by rw [←aU]; exact cap_left a ad.triangular_eq (w-1)
  have cuR : affineEval (L cu) R=0 := by rw [←aCaps,←aR]; exact cap_left a ad.triangular_eq (w-2)
  have cUne : c≠U := by
    intro he
    have idx := ad.injective (ac.trans (he.trans aU.symm))
    exact (by decide : ∀ w : ZMod 6, w≠w-1) w idx
  have bCap : b.opposite x=cu := by
    apply support_eq_of_two_points n L hL _ _ c U cUne
    · rw [←bc]; exact cap_left b bd.triangular_eq x
    · rw [←bU]; exact cap_right b bd.triangular_eq x
    · exact cuC
    · exact cuU
  have cuA : affineEval (L cu) a.center≠0 := cap_avoids a ad.triangular_eq (w-1)
  have cuB : affineEval (L cu) b.center≠0 := by rw [←bCap]; exact cap_avoids b bd.triangular_eq x
  have between : ∃ t : ℝ, 0<t ∧ t<1 ∧ U=segmentPoint R c t := by
    have h := ordinary_cap_between a ad.triangular_eq ad.positive (w-1) hOrdA
    simpa only [wprev,sub_add_cancel,aU,aR,ac] using h
  obtain ⟨t,ht0,ht1,Ueq⟩ := between
  have axisRel := axisU
  rw [Ueq,affineEval_segment] at axisRel
  have axisR : affineEval (L axis) R≠0 := by
    intro he
    rw [he, mul_zero,zero_add] at axisRel
    exact axisC ((mul_eq_zero.mp axisRel).resolve_left ht0.ne')
  have ca_cb : ca≠cb := by
    intro he
    have onA := a.radial_center w
    have onB : affineEval (L ca) b.center=0 := by rw [he]; exact b.radial_center x
    have eq := support_eq_of_two_points n L hL ca axis a.center b.center ab onA onB axisA axisB
    exact axisC (by rw [←eq]; exact caC)
  have ca_cu : ca≠cu := fun he=>cuA (by rw [←he]; exact a.radial_center w)
  have cb_cu : cb≠cu := fun he=>cuB (by rw [←he]; exact b.radial_center x)
  have arR : affineEval (L ar) R=0 := by rw [←aR]; exact a.radial_point (w-2)
  have brR : affineEval (L br) R=0 := by rw [←bR]; exact b.radial_point (x+2)
  have ar_br : ar≠br := by
    intro he
    have onA := a.radial_center (w-2)
    have onB : affineEval (L ar) b.center=0 := by rw [he]; exact b.radial_center (x+2)
    have eq := support_eq_of_two_points n L hL ar axis a.center b.center ab onA onB axisA axisB
    exact axisR (by rw [←eq]; exact arR)
  have ar_cu : ar≠cu := fun he=>cuA (by rw [←he]; exact a.radial_center (w-2))
  have br_cu : br≠cu := fun he=>cuB (by rw [←he]; exact b.radial_center (x+2))
  have aCapChoice := mem_three_of_card_three (supports n L c) ca cb cu (a.opposite w) rc
    ca_cb ca_cu cb_cu (mem_filter.mpr ⟨mem_univ _,caC⟩)
    (mem_filter.mpr ⟨mem_univ _,cbC⟩) (mem_filter.mpr ⟨mem_univ _,cuC⟩)
    (mem_filter.mpr ⟨mem_univ _,by rw [←ac]; exact cap_left a ad.triangular_eq w⟩)
  have aCap : a.opposite w=cb := by
    rcases aCapChoice with he|he|he
    · exact False.elim (cap_avoids a ad.triangular_eq w (by rw [he]; exact a.radial_center w))
    · exact he
    · have capR : affineEval (L (a.opposite w)) R=0 := by rw [he]; exact cuR
      have capAnti : affineEval (L (a.opposite w)) (a.point (w+1))=0 := cap_right a ad.triangular_eq w
      have anti : affineEval (L (a.opposite w)) a.center=0 := by
        exact antipodal_line_center a (L (a.opposite w)) (w-2)
          (by rw [aR]; exact capR)
          (by simpa only [show w-2+3=w+1 by ring] using capAnti)
      exact False.elim (cap_avoids a ad.triangular_eq w anti)
  have bCapChoice := mem_three_of_card_three (supports n L R) ar br cu (b.opposite (x+2)) rr
    ar_br ar_cu br_cu (mem_filter.mpr ⟨mem_univ _,arR⟩)
    (mem_filter.mpr ⟨mem_univ _,brR⟩) (mem_filter.mpr ⟨mem_univ _,cuR⟩)
    (mem_filter.mpr ⟨mem_univ _,by rw [←bR]; exact cap_left b bd.triangular_eq (x+2)⟩)
  have bCapR : b.opposite (x+2)=ar := by
    rcases bCapChoice with he|he|he
    · exact he
    · exact False.elim (cap_avoids b bd.triangular_eq (x+2) (by rw [he]; exact b.radial_center (x+2)))
    · have capC : affineEval (L (b.opposite (x+2))) c=0 := by rw [he]; exact cuC
      have capAnti : affineEval (L (b.opposite (x+2))) (b.point (x+3))=0 := by
        have eq : (x+2)+1=x+3 := by ring
        simpa only [eq] using cap_right b bd.triangular_eq (x+2)
      have anti : affineEval (L (b.opposite (x+2))) b.center=0 := by
        exact antipodal_line_center b (L (b.opposite (x+2))) x
          (by rw [bc]; exact capC) capAnti
      exact False.elim (cap_avoids b bd.triangular_eq (x+2) anti)
  have ra_cb : affineEval (L cb) (a.point (w+1))=0 := by rw [←aCap]; exact cap_right a ad.triangular_eq w
  have ra_ar : affineEval (L ar) (a.point (w+1))=0 := by
    have h := antipodal_line_point a (L ar) (w-2) (a.radial_center (w-2)) (by rw [aR]; exact arR)
    simpa only [show w-2+3=w+1 by ring] using h
  have cb_ar : affineEval (L ar) (b.point (x+3))=0 := by
    rw [←bCapR]
    simpa only [show (x+2)+1=x+3 by ring] using cap_right b bd.triangular_eq (x+2)
  have cb_cb : affineEval (L cb) (b.point (x+3))=0 := by
    simpa using antipodal_line_point b (L cb) x (b.radial_center x) (b.radial_point x)
  have distinct : cb≠ar := by
    intro he
    have onA : affineEval (L cb) a.center=0 := by rw [he]; exact a.radial_center (w-2)
    have eq := support_eq_of_two_points n L hL cb axis a.center b.center ab onA (b.radial_center x) axisA axisB
    exact axisC (by rw [←eq]; exact cbC)
  have same : a.point (w+1)=b.point (x+3) :=
    two_lines_two_points _ _ _ _ (det_ne_of_distinct n L hL cb ar distinct) ra_cb cb_cb ra_ar cb_ar
  obtain ⟨s,hs,sa⟩ := a.antipodal (w-2)
  obtain ⟨u,hu,sb⟩ := b.antipodal x
  simp only [Nat.cast_ofNat] at sa sb
  have aEval : affineEval (L axis) (a.point (w+1))= -s*affineEval (L axis) R := by
    have he : w-2+(3 : ZMod 6)=w+1 := by ring
    rw [he] at sa
    rw [sa,UpperTripleFan.affineEval_antipodal,axisA,aR]
    ring
  have bEval : affineEval (L axis) (b.point (x+3))= -u*affineEval (L axis) c := by
    rw [sb,UpperTripleFan.affineEval_antipodal,axisB,bc]
    ring
  have evalSame := congrArg (affineEval (L axis)) same
  rw [aEval,bEval] at evalSame
  rcases lt_or_gt_of_ne axisC with negC|posC
  · have posR : 0<affineEval (L axis) R := by
      by_contra h
      have nonpos := mul_nonpos_of_nonneg_of_nonpos (by linarith : 0≤1-t) (le_of_not_gt h)
      have negative := mul_neg_of_pos_of_neg ht0 negC
      linarith
    have left := mul_neg_of_neg_of_pos (by linarith : -s<0) posR
    have right := mul_pos_of_neg_of_neg (by linarith : -u<0) negC
    linarith
  · have negR : affineEval (L axis) R<0 := by
      by_contra h
      have nonneg := mul_nonneg (by linarith : 0≤1-t) (le_of_not_gt h)
      have positive := mul_pos ht0 posC
      linarith
    have left := mul_pos_of_neg_of_neg (by linarith : -s<0) negR
    have right := mul_neg_of_neg_of_pos (by linarith : -u<0) posC
    linarith

#print axioms ordinary_middle_pair_impossible
end Kobon.UpperOpenMathN13OrdinaryMiddle
