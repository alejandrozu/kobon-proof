import Kobon.UpperOpenMathAntipodalFullNeighborPair

namespace Kobon.UpperOpenMathN13Antipodal
open Cells FanGeometry UpperFan UpperVertexBudget
  UpperOpenMathAntipodalAdjacency Finset
set_option maxHeartbeats 1000000

theorem cap_left_selected {n : ℕ} {L : ℕ → Line ℝ}
    (f : Sectors n 3 L) (z : ZMod 6) (hz : z∈f.triangular) :
    affineEval (L (f.opposite z)) (f.point z)=0 := by
  simpa only [f.triangle_support z hz,f.triangle_left z hz] using (f.triangle z).Aq

theorem cap_right_selected {n : ℕ} {L : ℕ → Line ℝ}
    (f : Sectors n 3 L) (z : ZMod 6) (hz : z∈f.triangular) :
    affineEval (L (f.opposite z)) (f.point (z+1))=0 := by
  simpa only [f.triangle_support z hz,f.triangle_right z hz] using (f.triangle z).Ar

theorem cap_avoids_selected {n : ℕ} {L : ℕ → Line ℝ}
    (f : Sectors n 3 L) (z : ZMod 6) (hz : z∈f.triangular) :
    affineEval (L (f.opposite z)) f.center≠0 := by
  simpa only [f.triangle_support z hz,f.triangle_center z hz] using (f.triangle z).Ap

theorem cap_eq_selected_ordinary {n : ℕ} {L : ℕ → Line ℝ}
    (f : Sectors n 3 L) (z : ZMod 6)
    (hp : z-1∈f.triangular) (hz : z∈f.triangular)
    (ho : OrdinaryAt n L (f.point z)) : f.opposite (z-1)=f.opposite z := by
  apply ordinary_nonradial_unique n L (f.point z) ho (f.radial z)
    (f.opposite (z-1)) (f.opposite z) (f.radial_point z)
  · simpa only [sub_add_cancel] using cap_right_selected f (z-1) hp
  · exact cap_left_selected f z hz
  · intro he
    exact cap_avoids_selected f (z-1) hp (by rw [he]; exact f.radial_center z)
  · intro he
    exact cap_avoids_selected f z hz (by rw [he]; exact f.radial_center z)

theorem nested_antipodes_ne (c a b x : Point) (s t : ℝ)
    (hs : 0<s) (ht : 0<t) (ha : a≠c)
    (hb : b=(c.1-t*(a.1-c.1),c.2-t*(a.2-c.2)))
    (hx : x=(b.1-s*(c.1-b.1),b.2-s*(c.2-b.2))) : x≠a := by
  intro he
  have hp : 0<1+t+s*t := by positivity
  have h1 : (1+t+s*t)*(a.1-c.1)=0 := by
    have he1 := congrArg Prod.fst he
    rw [hx,hb] at he1
    dsimp at he1
    nlinarith
  have h2 : (1+t+s*t)*(a.2-c.2)=0 := by
    have he2 := congrArg Prod.snd he
    rw [hx,hb] at he2
    dsimp at he2
    nlinarith
  exact ha (Prod.ext (sub_eq_zero.mp ((mul_eq_zero.mp h1).resolve_left hp.ne'))
    (sub_eq_zero.mp ((mul_eq_zero.mp h2).resolve_left hp.ne')))

/-- A partial recipient fan with ordinary tip 1 cannot have a full antipodal
    two-cap neighbor at its opposite tip 3 in this matched orientation.
    No fullness assumption is made on the recipient. -/
theorem opposite_pair_impossible {n : ℕ} {L : ℕ → Line ℝ}
    (hL : NoParallel n L) (f g : Sectors n 3 L)
    (f0 : (0 : ZMod 6)∈f.triangular) (f1 : (1 : ZMod 6)∈f.triangular)
    (f2 : (2 : ZMod 6)∈f.triangular)
    (ord1 : OrdinaryAt n L (f.point 1))
    (triple2 : (supports n L (f.point 2)).card=3)
    (nc0 : f.point 0≠f.center) (nc2 : f.point 2≠f.center)
    (inj : Function.Injective f.point)
    (gfull : g.triangular=univ) (w : ZMod 6)
    (gc : g.center=f.point 3) (gp : g.point w=f.center)
    (gr : g.point (w-1)=f.point 2)
    (go : OrdinaryAt n L (g.point (w-2))) : False := by
  classical
  have fc01 : f.opposite 0=f.opposite 1 := by
    simpa using cap_eq_selected_ordinary f 1 (by simpa using f0) f1 ord1
  have capA : affineEval (L (f.opposite 1)) (f.point 0)=0 := by
    rw [←fc01]
    exact cap_left_selected f 0 f0
  have capD : affineEval (L (f.opposite 1)) (f.point 2)=0 := by
    simpa using cap_right_selected f 1 f1
  have capC := cap_avoids_selected f 1 f1
  have gR : g.radial (w-1)=f.opposite 2 := by
    apply support_eq_of_two_points n L hL _ _ (f.point 3) (f.point 2)
      (fun he=>(by decide : (3 : ZMod 6)≠2) (inj he))
    · rw [←gc]; exact g.radial_center (w-1)
    · rw [←gr]; exact g.radial_point (w-1)
    · simpa using cap_right_selected f 2 f2
    · exact cap_left_selected f 2 f2
  have RneqS : f.radial 2≠g.radial (w-1) := by
    intro he
    apply cap_avoids_selected f 2 f2
    rw [←gR,←he]
    exact f.radial_center 2
  have RneqT : f.radial 2≠f.opposite 1 := by
    intro he
    exact capC (by rw [←he]; exact f.radial_center 2)
  have TneqS : f.opposite 1≠g.radial (w-1) := by
    intro he
    have capB : affineEval (L (f.opposite 1)) (f.point 3)=0 := by
      rw [he,←gc]; exact g.radial_center (w-1)
    exact capC (by simpa using antipodal_line_center f (L (f.opposite 1)) 0 capA capB)
  have SneqT : g.radial (w-1)≠f.opposite 1 := Ne.symm TneqS
  have gcapEq : g.opposite (w-3)=g.opposite (w-2) := by
    have hi : w-2-1=w-3 := by ring
    simpa only [hi] using cap_eq_at_ordinary g gfull (w-2) go
  have hX : w-3=w+3 := (by decide : ∀ w : ZMod 6, w-3=w+3) w
  have KX : affineEval (L (g.opposite (w-2))) (g.point (w+3))=0 := by
    rw [←gcapEq,←hX]
    exact cap_left g gfull (w-3)
  have KR : g.opposite (w-2)≠f.radial 2 := by
    intro he
    have Kc : affineEval (L (g.opposite (w-2))) (g.point w)=0 := by
      rw [he,gp]; exact f.radial_center 2
    exact cap_avoids g gfull (w-2)
      (antipodal_line_center g (L (g.opposite (w-2))) w Kc KX)
  have KS : g.opposite (w-2)≠g.radial (w-1) := by
    intro he
    exact cap_avoids g gfull (w-2) (by rw [he]; exact g.radial_center (w-1))
  have KD : affineEval (L (g.opposite (w-2))) (f.point 2)=0 := by
    rw [←gr]
    have hi : w-2+1=w-1 := by ring
    simpa only [hi] using cap_right g gfull (w-2)
  have member (i : Fin n) (hi : affineEval (L i) (f.point 2)=0) :
      i∈supports n L (f.point 2) := by simp [supports,hi]
  have cases := mem_three_of_card_three (supports n L (f.point 2))
    (f.radial 2) (g.radial (w-1)) (f.opposite 1) (g.opposite (w-2)) triple2
    RneqS RneqT SneqT (member _ (f.radial_point 2))
    (member _ (by rw [←gr]; exact g.radial_point (w-1)))
    (member _ capD) (member _ KD)
  have KT : g.opposite (w-2)=f.opposite 1 := cases.resolve_left KR |>.resolve_left KS
  have AX : affineEval (L (f.opposite 1)) (g.point (w+3))=0 := by rw [←KT]; exact KX
  have axis : g.radial w=f.radial 0 := by
    apply support_eq_of_two_points n L hL _ _ (f.point 3) f.center
      (fun he=>nc0 (by
        obtain ⟨t,ht,hb⟩ := f.antipodal 0
        simp only [zero_add,Nat.cast_ofNat] at hb
        have h1 := congrArg Prod.fst (hb.symm.trans he)
        have h2 := congrArg Prod.snd (hb.symm.trans he)
        dsimp at h1 h2
        exact Prod.ext (by nlinarith) (by nlinarith)))
    · rw [←gc]; exact g.radial_center w
    · rw [←gp]; exact g.radial_point w
    · simpa using antipodal_line_point f (L (f.radial 0)) 0
        (f.radial_center 0) (f.radial_point 0)
    · exact f.radial_center 0
  have RX : affineEval (L (f.radial 0)) (g.point (w+3))=0 := by
    rw [←axis]
    exact antipodal_line_point g (L (g.radial w)) w
      (g.radial_center w) (g.radial_point w)
  have RT : f.radial 0≠f.opposite 1 := by
    intro he; exact capC (by rw [←he]; exact f.radial_center 0)
  have XA : g.point (w+3)=f.point 0 := two_lines_two_points _ _ _ _
    (det_ne_of_distinct n L hL _ _ RT) RX (f.radial_point 0) AX capA
  obtain ⟨t,ht,hb⟩ := f.antipodal 0
  obtain ⟨s,hs,hx⟩ := g.antipodal w
  simp only [zero_add,Nat.cast_ofNat] at hb hx
  rw [gc,gp] at hx
  exact nested_antipodes_ne f.center (f.point 0) (f.point 3) _ s t hs ht nc0 hb hx XA

#print axioms opposite_pair_impossible
end Kobon.UpperOpenMathN13Antipodal

