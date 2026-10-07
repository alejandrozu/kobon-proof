import Kobon.UpperOpenMathPartialTriple

/-! The following-neighbor version of the partial triple obstruction.
Together with its preceding-neighbor version this controls both physical
cap tips across a shared core edge. -/
namespace Kobon.UpperOpenMathPartialTripleMirror
open Cells FanGeometry UpperFan Finset

@[simp] theorem one_add_one : (1 : ZMod 6)+1=2 := by decide
@[simp] theorem five_add_three : (5 : ZMod 6)+3=2 := by decide

theorem next_on_opposite_of_ordinary_shared {n r : ℕ} [NeZero (2*r)]
    {L : ℕ → Line ℝ} (f : UpperFan.Sectors n r L) (z : ZMod (2*r))
    (hz : z∈f.ordinaryShared) :
    affineEval (L (f.opposite (z-1))) (f.point (z+1))=0 := by
  have ho := ((f.mem_ordinaryShared z).mp hz).2.2
  have hp : z-1∈f.ordinaryShared ∨ z-1+1∈f.ordinaryShared := by right; simpa using hz
  have hc : z∈f.ordinaryShared ∨ z+1∈f.ordinaryShared := Or.inl hz
  have he : f.opposite (z-1)=f.opposite z := by
    apply ordinary_nonradial_unique n L (f.point z) ho (f.radial z)
    · exact f.radial_point z
    · simpa [UpperFan.Sectors.asCyclic] using f.asCyclic.opposite_right (z-1) hp
    · exact f.asCyclic.opposite_left z hc
    · intro h
      have hh := f.radial_center z
      rw [← h] at hh
      exact f.asCyclic.opposite_avoids_center (z-1) hp hh
    · intro h
      have hh := f.radial_center z
      rw [← h] at hh
      exact f.asCyclic.opposite_avoids_center z hc hh
  rw [he]
  exact f.asCyclic.opposite_right z hc

theorem incompatible_following_partial_triple_fans {n : ℕ} {L : ℕ → Line ℝ}
    (hL : NoParallel n L) (f g : UpperFan.Sectors n 3 L)
    (fselected : (1 : ZMod 6)∈f.ordinaryShared)
    (gselected : (1 : ZMod 6)∈g.ordinaryShared)
    (centerg : g.center=f.point 0) (pointg : g.point 0=f.center)
    (rightg : g.point 5=f.point 1) (leftg : g.point 1=f.point 5)
    (pos : 0<areaDet f.center (f.point 0) (f.point 1))
    (neg : areaDet f.center (f.point 0) (f.point 5)<0) : False := by
  have hfuse : (0 : ZMod 6)∈f.ordinaryShared ∨ 0+1∈f.ordinaryShared := by right; simpa using fselected
  have hguse : (0 : ZMod 6)∈g.ordinaryShared ∨ 0+1∈g.ordinaryShared := by right; simpa using gselected
  have fU : affineEval (L (f.opposite 0)) (f.point 1)=0 := by
    simpa [UpperFan.Sectors.asCyclic] using f.asCyclic.opposite_right 0 hfuse
  have fD : affineEval (L (f.opposite 0)) (f.point 0)=0 := f.asCyclic.opposite_left 0 hfuse
  have fB : affineEval (L (f.opposite 0)) (f.point 2)=0 := by
    have hp : f.point 2=f.point ((1 : ZMod (2*3))+1) := congrArg f.point (by decide)
    have ho : f.opposite 0=f.opposite ((1 : ZMod (2*3))-1) := congrArg f.opposite (by decide)
    rw [hp,ho]
    exact next_on_opposite_of_ordinary_shared f 1 fselected
  have gV : affineEval (L (g.opposite 0)) (f.point 5)=0 := by
    simpa [UpperFan.Sectors.asCyclic,leftg] using g.asCyclic.opposite_right 0 hguse
  have gC : affineEval (L (g.opposite 0)) f.center=0 := by
    simpa [UpperFan.Sectors.asCyclic,pointg] using g.asCyclic.opposite_left 0 hguse
  have gE : affineEval (L (g.opposite 0)) (g.point 2)=0 := by
    have hp : g.point 2=g.point ((1 : ZMod (2*3))+1) := congrArg g.point (by decide)
    have ho : g.opposite 0=g.opposite ((1 : ZMod (2*3))-1) := congrArg g.opposite (by decide)
    rw [hp,ho]
    exact next_on_opposite_of_ordinary_shared g 1 gselected
  obtain ⟨b,hb,hB⟩ := f.antipodal 5
  obtain ⟨d,hd,hE⟩ := g.antipodal 5
  have hB' : f.point 2=(f.center.1-b*((f.point 5).1-f.center.1),
      f.center.2-b*((f.point 5).2-f.center.2)) := by simpa using hB
  have hE' : g.point 2=((f.point 0).1-d*((f.point 1).1-(f.point 0).1),
      (f.point 0).2-d*((f.point 1).2-(f.point 0).2)) := by simpa [centerg,rightg] using hE
  have gB : affineEval (L (g.opposite 0)) (f.point 2)=0 := by
    rw [hB',UpperTripleFan.affineEval_antipodal,gC,gV]
    ring
  have fE : affineEval (L (f.opposite 0)) (g.point 2)=0 := by
    rw [hE',UpperTripleFan.affineEval_antipodal,fD,fU]
    ring
  have hne : f.opposite 0≠g.opposite 0 := by
    intro he
    apply f.asCyclic.opposite_avoids_center 0 hfuse
    simpa only [UpperFan.Sectors.asCyclic,he] using gC
  have hBE : f.point 2=g.point 2 := two_lines_two_points
    (L (f.opposite 0)) (L (g.opposite 0)) _ _
    (noParallel_any n L hL _ _ (f.opposite 0).isLt (g.opposite 0).isLt
      (fun h => hne (Fin.ext h))) fB fE gB gE
  have hareaB : areaDet f.center (f.point 0) (f.point 2)=
      -b*areaDet f.center (f.point 0) (f.point 5) := by rw [hB']; dsimp [areaDet]; ring
  have hareaE : areaDet f.center (f.point 0) (g.point 2)=
      -d*areaDet f.center (f.point 0) (f.point 1) := by rw [hE']; dsimp [areaDet]; ring
  rw [hBE,hareaE] at hareaB
  have hbn := mul_neg_of_pos_of_neg hb neg
  have hdp := mul_pos hd pos
  nlinarith

theorem incompatible_following_partial_triple_fans_at {n : ℕ} {L : ℕ → Line ℝ}
    (hL : NoParallel n L) (f g : UpperFan.Sectors n 3 L) (a b : ZMod 6)
    (fselected : a+1∈f.ordinaryShared) (gselected : b+1∈g.ordinaryShared)
    (centerg : g.center=f.point a) (pointg : g.point b=f.center)
    (rightg : g.point (b-1)=f.point (a+1))
    (leftg : g.point (b+1)=f.point (a-1))
    (positive : ∀ z, 0<areaDet f.center (f.point z) (f.point (z+1))) : False := by
  apply incompatible_following_partial_triple_fans hL
    (UpperOpenMathRotation.Sectors.shift f a) (UpperOpenMathRotation.Sectors.shift g b)
  · exact (UpperOpenMathRotation.Sectors.shift_mem_ordinaryShared f a 1).mpr fselected
  · exact (UpperOpenMathRotation.Sectors.shift_mem_ordinaryShared g b 1).mpr gselected
  · simpa using centerg
  · simpa using pointg
  · have he : b+(5 : ZMod 6)=b-1 := by
      have h5 : (5 : ZMod 6)= -1 := by decide
      rw [h5]; ring
    simpa only [UpperOpenMathRotation.Sectors.shift_point,he] using rightg
  · have he : a+(5 : ZMod 6)=a-1 := by
      have h5 : (5 : ZMod 6)= -1 := by decide
      rw [h5]; ring
    simpa only [UpperOpenMathRotation.Sectors.shift_point,he] using leftg
  · simpa using positive a
  · have hp := positive (a-1)
    have he : a-1+1=a := by ring
    rw [he] at hp
    have ha : areaDet f.center (f.point a) (f.point (a-1))=
        -areaDet f.center (f.point (a-1)) (f.point a) := by dsimp [areaDet]; ring
    have h5 : a+(5 : ZMod 6)=a-1 := by
      have hh : (5 : ZMod 6)= -1 := by decide
      rw [hh]; ring
    have hn : -areaDet f.center (f.point (a-1)) (f.point a)<0 := by linarith
    simpa only [UpperOpenMathRotation.Sectors.shift_center,
      UpperOpenMathRotation.Sectors.shift_point,add_zero,h5,ha] using hn

theorem incompatible_following_partial_triple_fans_card {n r s : ℕ}
    [NeZero (2*r)] [NeZero (2*s)] {L : ℕ → Line ℝ}
    (hr : r=3) (hs : s=3) (hL : NoParallel n L)
    (f : UpperFan.Sectors n r L) (g : UpperFan.Sectors n s L)
    (a : ZMod (2*r)) (b : ZMod (2*s))
    (fselected : a+1∈f.ordinaryShared) (gselected : b+1∈g.ordinaryShared)
    (centerg : g.center=f.point a) (pointg : g.point b=f.center)
    (rightg : g.point (b-1)=f.point (a+1))
    (leftg : g.point (b+1)=f.point (a-1))
    (positive : ∀ z, 0<areaDet f.center (f.point z) (f.point (z+1))) : False := by
  subst r
  subst s
  exact incompatible_following_partial_triple_fans_at hL f g a b fselected gselected centerg pointg rightg leftg positive

#print axioms incompatible_following_partial_triple_fans_card
end Kobon.UpperOpenMathPartialTripleMirror
