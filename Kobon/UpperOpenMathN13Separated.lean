import Kobon.UpperOpenMathAntipodalFullNeighborPair
import Kobon.UpperFanSupport

namespace Kobon.UpperOpenMathN13Separated
open Cells FanGeometry UpperFan UpperVertexBudget
  UpperOpenMathAntipodalAdjacency
  UpperOpenMathAntipodalBalancedAdjacency Finset
set_option maxHeartbeats 1000000

/-- Two outward continuations forced by the separated-core case have
    incompatible oriented areas. This is invariant under affine charts. -/
theorem separated_continuations_impossible (c a d b x y : Point) (s t : ℝ)
    (hs : 0<s) (ht : 0<t)
    (left : 0<areaDet c a d) (right : 0<areaDet c d b)
    (hx : x=(a.1-s*(c.1-a.1),a.2-s*(c.2-a.2)))
    (hy : y=(b.1-t*(d.1-b.1),b.2-t*(d.2-b.2)))
    (colX : areaDet b d x=0) (colY : areaDet c a y=0) : False := by
  have hX : areaDet b d x= -(1+s)*(areaDet c a d-areaDet c a b)-areaDet c d b := by
    rw [hx]; dsimp [areaDet]; ring
  have hY : areaDet c a y=(1+t)*areaDet c a b-t*areaDet c a d := by
    rw [hy]; dsimp [areaDet]; ring
  rw [hX] at colX
  rw [hY] at colY
  have hLess : areaDet c a d<areaDet c a b := by
    have hp : 0<1+s := by linarith
    by_contra h
    have prod := mul_nonneg hp.le (sub_nonneg.mpr (le_of_not_gt h))
    nlinarith
  have hMore : areaDet c a b<areaDet c a d := by
    have hab : 0<areaDet c a b := by
      have hpos : 0<t*areaDet c a d := mul_pos ht left
      have hp : 0<1+t := by linarith
      have he : (1+t)*areaDet c a b=t*areaDet c a d := by linarith
      have hm : 0<(1+t)*areaDet c a b := by rw [he]; exact hpos
      exact (mul_pos_iff_of_pos_left hp).mp hm
    nlinarith
  linarith

/-- The third indexed support at the intermediate core identifies the
    nonradial continuation of the full neighbor with the other selected base. -/
theorem continuation_on_other_cap {n : ℕ} {L : ℕ → Line ℝ}
    (hL : NoParallel n L) (f g : Sectors n 3 L)
    (f0 : (0 : ZMod 6)∈f.triangular) (f1 : (1 : ZMod 6)∈f.triangular)
    (triple1 : (supports n L (f.point 1)).card=3)
    (inj : Function.Injective f.point)
    (capne : f.opposite 0≠f.opposite 1)
    (gfull : g.triangular=univ) (w : ZMod 6)
    (gc : g.center=f.point 0) (gp : g.point w=f.center)
    (gr : g.point (w-1)=f.point 1)
    (go : OrdinaryAt n L (g.point (w-2))) :
    affineEval (L (f.opposite 1)) (g.point (w+3))=0 := by
  classical
  have gR : g.radial (w-1)=f.opposite 0 := by
    apply support_eq_of_two_points n L hL _ _ (f.point 0) (f.point 1)
      (fun he=>(by decide : (0 : ZMod 6)≠1) (inj he))
    · rw [←gc]; exact g.radial_center (w-1)
    · rw [←gr]; exact g.radial_point (w-1)
    · exact cap_left_at f 0 f0
    · simpa using cap_right_at f 0 f0
  have RneqS : f.radial 1≠g.radial (w-1) := by
    intro he
    apply cap_avoids_at f 0 f0
    rw [←gR,←he]; exact f.radial_center 1
  have RneqT : f.radial 1≠f.opposite 1 := by
    intro he
    exact cap_avoids_at f 1 f1 (by rw [←he]; exact f.radial_center 1)
  have SneqT : g.radial (w-1)≠f.opposite 1 := by rw [gR]; exact capne
  have gcapEq : g.opposite (w-3)=g.opposite (w-2) := by
    have hi : w-2-1=w-3 := by ring
    simpa only [hi] using cap_eq_at_ordinary g gfull (w-2) go
  have hX : w-3=w+3 := (by decide : ∀ w : ZMod 6, w-3=w+3) w
  have KX : affineEval (L (g.opposite (w-2))) (g.point (w+3))=0 := by
    rw [←gcapEq,←hX]
    exact cap_left g gfull (w-3)
  have KR : g.opposite (w-2)≠f.radial 1 := by
    intro he
    have Kc : affineEval (L (g.opposite (w-2))) (g.point w)=0 := by
      rw [he,gp]; exact f.radial_center 1
    exact cap_avoids g gfull (w-2)
      (antipodal_line_center g (L (g.opposite (w-2))) w Kc KX)
  have KS : g.opposite (w-2)≠g.radial (w-1) := by
    intro he
    exact cap_avoids g gfull (w-2) (by rw [he]; exact g.radial_center (w-1))
  have KD : affineEval (L (g.opposite (w-2))) (f.point 1)=0 := by
    rw [←gr]
    have hi : w-2+1=w-1 := by ring
    simpa only [hi] using cap_right g gfull (w-2)
  have member (i : Fin n) (hi : affineEval (L i) (f.point 1)=0) :
      i∈supports n L (f.point 1) := by simp [supports,hi]
  have cases := mem_three_of_card_three (supports n L (f.point 1))
    (f.radial 1) (g.radial (w-1)) (f.opposite 1) (g.opposite (w-2)) triple1
    RneqS RneqT SneqT (member _ (f.radial_point 1))
    (member _ (by rw [←gr]; exact g.radial_point (w-1)))
    (member _ (cap_left_at f 1 f1)) (member _ KD)
  have KT : g.opposite (w-2)=f.opposite 1 := cases.resolve_left KR |>.resolve_left KS
  rw [←KT]; exact KX

/-- The full fan at the other separated core supplies the opposing outward
    continuation on the recipient's first radial support. -/
theorem continuation_on_first_radial {n : ℕ} {L : ℕ → Line ℝ}
    (hL : NoParallel n L) (f k : Sectors n 3 L)
    (nc3 : f.point 3≠f.center)
    (kfull : k.triangular=univ) (w : ZMod 6)
    (kc : k.center=f.point 2) (kp : k.point w=f.center)
    (kl : k.point (w-1)=f.point 3)
    (ko : OrdinaryAt n L (k.point (w-1))) :
    affineEval (L (f.radial 0)) (k.point (w-2))=0 := by
  have K : k.opposite (w-1)=f.radial 0 := by
    apply support_eq_of_two_points n L hL _ _ (f.point 3) f.center nc3
    · rw [←kl]; exact cap_left k kfull (w-1)
    · rw [←kp]; simpa only [sub_add_cancel] using cap_right k kfull (w-1)
    · simpa using antipodal_line_point f (L (f.radial 0)) 0
        (f.radial_center 0) (f.radial_point 0)
    · exact f.radial_center 0
  have he : k.opposite (w-2)=k.opposite (w-1) := by
    have hi : w-1-1=w-2 := by ring
    simpa only [hi] using cap_eq_at_ordinary k kfull (w-1) ko
  rw [←K,←he]
  exact cap_left k kfull (w-2)

theorem area_zero_of_valid_line (l : Line ℝ) (p q r : Point)
    (valid : l.a≠0∨l.b≠0)
    (hp : affineEval l p=0) (hq : affineEval l q=0) (hr : affineEval l r=0) :
    areaDet p q r=0 := by
  by_contra h
  obtain ⟨ha,hb⟩ := three_zeros_force_zero_normal l p q r h hp hq hr
  exact valid.elim (fun h=>h ha) (fun h=>h hb)

/-- The separated pair with a core intermediate tip is impossible for actual
    compatible full two-cap charts, even though the recipient is partial. -/
theorem separated_core_pair_impossible {n : ℕ} {L : ℕ → Line ℝ}
    (hL : NoParallel n L) (hn : 2≤n) (f g k : Sectors n 3 L)
    (f0 : (0 : ZMod 6)∈f.triangular) (f1 : (1 : ZMod 6)∈f.triangular)
    (triple1 : (supports n L (f.point 1)).card=3)
    (inj : Function.Injective f.point) (nc3 : f.point 3≠f.center)
    (positive0 : 0<areaDet f.center (f.point 0) (f.point 1))
    (positive1 : 0<areaDet f.center (f.point 1) (f.point 2))
    (capne : f.opposite 0≠f.opposite 1)
    (gfull : g.triangular=univ) (w : ZMod 6)
    (gc : g.center=f.point 0) (gp : g.point w=f.center)
    (gr : g.point (w-1)=f.point 1)
    (go : OrdinaryAt n L (g.point (w-2)))
    (kfull : k.triangular=univ) (x : ZMod 6)
    (kc : k.center=f.point 2) (kp : k.point x=f.center)
    (kl : k.point (x-1)=f.point 3) (kr : k.point (x+1)=f.point 1)
    (ko : OrdinaryAt n L (k.point (x-1))) : False := by
  have hxcap := continuation_on_other_cap hL f g f0 f1 triple1 inj capne
    gfull w gc gp gr go
  have hycap := continuation_on_first_radial hL f k nc3 kfull x kc kp kl ko
  have colX : areaDet (f.point 2) (f.point 1) (g.point (w+3))=0 := by
    apply UpperFanSupport.collinear_of_incident_line (L (f.opposite 1)) f.center
    · exact cap_avoids_at f 1 f1
    · simpa using cap_right_at f 1 f1
    · exact cap_left_at f 1 f1
    · exact hxcap
  have colY : areaDet f.center (f.point 0) (k.point (x-2))=0 :=
    area_zero_of_valid_line _ _ _ _ (line_valid n L hL hn (f.radial 0))
      (f.radial_center 0) (f.radial_point 0) hycap
  obtain ⟨s,hs,hx⟩ := g.antipodal w
  obtain ⟨t,ht,hy⟩ := k.antipodal (x+1)
  have hi : x+1+3=x-2 := (by decide : ∀ x : ZMod 6, x+1+3=x-2) x
  simp only [Nat.cast_ofNat] at hx hy
  rw [gc,gp] at hx
  rw [hi,kc,kr] at hy
  exact separated_continuations_impossible f.center (f.point 0) (f.point 1)
    (f.point 2) _ _ s t hs ht positive0 positive1 hx hy colX colY

theorem separated_continuations_impossible_negative (c a d b x y : Point) (s t : ℝ)
    (hs : 0<s) (ht : 0<t)
    (left : areaDet c a d<0) (right : areaDet c d b<0)
    (hx : x=(a.1-s*(c.1-a.1),a.2-s*(c.2-a.2)))
    (hy : y=(b.1-t*(d.1-b.1),b.2-t*(d.2-b.2)))
    (colX : areaDet b d x=0) (colY : areaDet c a y=0) : False := by
  have hX : areaDet b d x= -(1+s)*(areaDet c a d-areaDet c a b)-areaDet c d b := by
    rw [hx]; dsimp [areaDet]; ring
  have hY : areaDet c a y=(1+t)*areaDet c a b-t*areaDet c a d := by
    rw [hy]; dsimp [areaDet]; ring
  rw [hX] at colX
  rw [hY] at colY
  have hLess : areaDet c a b<areaDet c a d := by
    have hp : 0<1+s := by linarith
    by_contra h
    have prod := mul_nonpos_of_nonneg_of_nonpos hp.le
      (sub_nonpos.mpr (le_of_not_gt h))
    nlinarith
  have hMore : areaDet c a d<areaDet c a b := by
    have hab : areaDet c a b<0 := by
      have hneg : t*areaDet c a d<0 := mul_neg_of_pos_of_neg ht left
      have hp : 0<1+t := by linarith
      have he : (1+t)*areaDet c a b=t*areaDet c a d := by linarith
      have hm : (1+t)*areaDet c a b<0 := by rw [he]; exact hneg
      by_contra h
      have hnon := mul_nonneg hp.le (le_of_not_gt h)
      linarith
    by_contra h
    have prod := mul_nonneg ht.le (sub_nonneg.mpr (le_of_not_gt h))
    nlinarith
  linarith
theorem separated_core_pair_impossible_negative {n : ℕ} {L : ℕ → Line ℝ}
    (hL : NoParallel n L) (hn : 2≤n) (f g k : Sectors n 3 L)
    (f0 : (0 : ZMod 6)∈f.triangular) (f1 : (1 : ZMod 6)∈f.triangular)
    (triple1 : (supports n L (f.point 1)).card=3)
    (inj : Function.Injective f.point) (nc3 : f.point 3≠f.center)
    (negative0 : areaDet f.center (f.point 0) (f.point 1)<0)
    (negative1 : areaDet f.center (f.point 1) (f.point 2)<0)
    (capne : f.opposite 0≠f.opposite 1)
    (gfull : g.triangular=univ) (w : ZMod 6)
    (gc : g.center=f.point 0) (gp : g.point w=f.center)
    (gr : g.point (w-1)=f.point 1)
    (go : OrdinaryAt n L (g.point (w-2)))
    (kfull : k.triangular=univ) (x : ZMod 6)
    (kc : k.center=f.point 2) (kp : k.point x=f.center)
    (kl : k.point (x-1)=f.point 3) (kr : k.point (x+1)=f.point 1)
    (ko : OrdinaryAt n L (k.point (x-1))) : False := by
  have hxcap := continuation_on_other_cap hL f g f0 f1 triple1 inj capne
    gfull w gc gp gr go
  have hycap := continuation_on_first_radial hL f k nc3 kfull x kc kp kl ko
  have colX : areaDet (f.point 2) (f.point 1) (g.point (w+3))=0 := by
    apply UpperFanSupport.collinear_of_incident_line (L (f.opposite 1)) f.center
    · exact cap_avoids_at f 1 f1
    · simpa using cap_right_at f 1 f1
    · exact cap_left_at f 1 f1
    · exact hxcap
  have colY : areaDet f.center (f.point 0) (k.point (x-2))=0 :=
    area_zero_of_valid_line _ _ _ _ (line_valid n L hL hn (f.radial 0))
      (f.radial_center 0) (f.radial_point 0) hycap
  obtain ⟨s,hs,hx⟩ := g.antipodal w
  obtain ⟨t,ht,hy⟩ := k.antipodal (x+1)
  have hi : x+1+3=x-2 := (by decide : ∀ x : ZMod 6, x+1+3=x-2) x
  simp only [Nat.cast_ofNat] at hx hy
  rw [gc,gp] at hx
  rw [hi,kc,kr] at hy
  exact separated_continuations_impossible_negative f.center (f.point 0) (f.point 1)
    (f.point 2) _ _ s t hs ht negative0 negative1 hx hy colX colY


#print axioms separated_core_pair_impossible_negative
#print axioms separated_core_pair_impossible
#print axioms separated_continuations_impossible
#print axioms continuation_on_other_cap
#print axioms continuation_on_first_radial
end Kobon.UpperOpenMathN13Separated




