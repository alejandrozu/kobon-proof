import Kobon.UpperOpenMathRotation

/-!
# A shared-edge obstruction for partial triple fans

The older incompatibility theorem assumed complete extremal triple fans.
Its geometric proof in fact needs only the ordinary shared neighboring ray
on the two opposing physical sides of the matched edge. Those hypotheses
can occur in four- or five-sector partial fans as well. No full-fan or
extremal-degree premise is used below.

Raj Srirangam's OpenMath note proves the related two-four-run-endpoint
obstruction in `proofs/all8/ALL8_NOTE7.md`, section 4, at repository revision
`eed14659a9b2f4ca12777da5d557f2b620b966f6`. The wrong-ray/shared-apex geometric
idea is shared with that work; the statement here removes its component-mask
restrictions and checks the broader local interface in Lean.
-/
namespace Kobon.UpperOpenMathPartialTriple
open Cells FanGeometry UpperFan Finset

theorem previous_on_opposite_of_ordinary_shared {n r : ℕ} [NeZero (2*r)]
    {L : ℕ → Line ℝ} (f : UpperFan.Sectors n r L) (z : ZMod (2*r))
    (hz : z∈f.ordinaryShared) :
    affineEval (L (f.opposite z)) (f.point (z-1))=0 := by
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
  rw [← he]
  exact f.asCyclic.opposite_left (z-1) hp

/-- Fullness of either fan is unnecessary: the selected ordinary neighboring
radial side already supplies exactly the two cap triangles used in the
propagation contradiction. -/
theorem incompatible_partial_triple_fans {n : ℕ} {L : ℕ → Line ℝ}
    (hL : NoParallel n L) (f g : UpperFan.Sectors n 3 L)
    (fselected : (5 : ZMod 6)∈f.ordinaryShared)
    (gselected : (5 : ZMod 6)∈g.ordinaryShared)
    (centerg : g.center=f.point 0) (pointg : g.point 0=f.center)
    (rightg : g.point 5=f.point 1) (leftg : g.point 1=f.point 5)
    (pos : 0<areaDet f.center (f.point 0) (f.point 1))
    (neg : areaDet f.center (f.point 0) (f.point 5)<0) : False := by
  have hfuse : (5 : ZMod 6)∈f.ordinaryShared ∨ 5+1∈f.ordinaryShared := Or.inl fselected
  have hguse : (5 : ZMod 6)∈g.ordinaryShared ∨ 5+1∈g.ordinaryShared := Or.inl gselected
  have fS : affineEval (L (f.opposite 5)) (f.point 5)=0 := f.asCyclic.opposite_left 5 hfuse
  have fQ : affineEval (L (f.opposite 5)) (f.point 0)=0 := by
    simpa [UpperFan.Sectors.asCyclic] using f.asCyclic.opposite_right 5 hfuse
  have fB : affineEval (L (f.opposite 5)) (f.point 4)=0 := by
    simpa using previous_on_opposite_of_ordinary_shared f 5 fselected
  have gR : affineEval (L (g.opposite 5)) (f.point 1)=0 := by
    simpa [UpperFan.Sectors.asCyclic,rightg] using g.asCyclic.opposite_left 5 hguse
  have gP : affineEval (L (g.opposite 5)) f.center=0 := by
    simpa [UpperFan.Sectors.asCyclic,pointg] using g.asCyclic.opposite_right 5 hguse
  have gD : affineEval (L (g.opposite 5)) (g.point 4)=0 := by
    simpa using previous_on_opposite_of_ordinary_shared g 5 gselected
  obtain ⟨b,hb,hB⟩ := f.antipodal 1
  obtain ⟨d,hd,hD⟩ := g.antipodal 1
  have hB' : f.point 4=(f.center.1-b*((f.point 1).1-f.center.1),
      f.center.2-b*((f.point 1).2-f.center.2)) := by simpa using hB
  have hD' : g.point 4=((f.point 0).1-d*((f.point 5).1-(f.point 0).1),
      (f.point 0).2-d*((f.point 5).2-(f.point 0).2)) := by simpa [centerg,leftg] using hD
  have gB : affineEval (L (g.opposite 5)) (f.point 4)=0 := by
    rw [hB',UpperTripleFan.affineEval_antipodal,gP,gR]
    ring
  have fD : affineEval (L (f.opposite 5)) (g.point 4)=0 := by
    rw [hD',UpperTripleFan.affineEval_antipodal,fQ,fS]
    ring
  have hne : f.opposite 5≠g.opposite 5 := by
    intro he
    have hh := f.asCyclic.opposite_avoids_center 5 hfuse
    apply hh
    simpa only [UpperFan.Sectors.asCyclic,he] using gP
  have hBD : f.point 4=g.point 4 := two_lines_two_points
    (L (f.opposite 5)) (L (g.opposite 5)) _ _
    (noParallel_any n L hL _ _ (f.opposite 5).isLt (g.opposite 5).isLt
      (fun h => hne (Fin.ext h))) fB fD gB gD
  have hareaB : areaDet f.center (f.point 0) (f.point 4)=
      -b*areaDet f.center (f.point 0) (f.point 1) := by rw [hB']; dsimp [areaDet]; ring
  have hareaD : areaDet f.center (f.point 0) (g.point 4)=
      -d*areaDet f.center (f.point 0) (f.point 5) := by rw [hD']; dsimp [areaDet]; ring
  rw [hBD,hareaD] at hareaB
  have hbp := mul_pos hb pos
  have hdn := mul_neg_of_pos_of_neg hd neg
  nlinarith

theorem incompatible_partial_triple_fans_at {n : ℕ} {L : ℕ → Line ℝ}
    (hL : NoParallel n L) (f g : UpperFan.Sectors n 3 L) (a b : ZMod 6)
    (fselected : a-1∈f.ordinaryShared) (gselected : b-1∈g.ordinaryShared)
    (centerg : g.center=f.point a) (pointg : g.point b=f.center)
    (rightg : g.point (b-1)=f.point (a+1))
    (leftg : g.point (b+1)=f.point (a-1))
    (positive : ∀ z, 0<areaDet f.center (f.point z) (f.point (z+1))) : False := by
  apply incompatible_partial_triple_fans hL
    (UpperOpenMathRotation.Sectors.shift f a) (UpperOpenMathRotation.Sectors.shift g b)
  · apply (UpperOpenMathRotation.Sectors.shift_mem_ordinaryShared f a 5).mpr
    have he : a+(5 : ZMod 6)=a-1 := by
      have h5 : (5 : ZMod 6)= -1 := by decide
      rw [h5]
      ring
    simpa only [he] using fselected
  · apply (UpperOpenMathRotation.Sectors.shift_mem_ordinaryShared g b 5).mpr
    have he : b+(5 : ZMod 6)=b-1 := by
      have h5 : (5 : ZMod 6)= -1 := by decide
      rw [h5]
      ring
    simpa only [he] using gselected
  · simpa using centerg
  · simpa using pointg
  · have he : b+(5 : ZMod 6)=b-1 := by
      have h5 : (5 : ZMod 6)= -1 := by decide
      rw [h5]
      ring
    simpa only [UpperOpenMathRotation.Sectors.shift_point,he] using rightg
  · have he : a+(5 : ZMod 6)=a-1 := by
      have h5 : (5 : ZMod 6)= -1 := by decide
      rw [h5]
      ring
    simpa only [UpperOpenMathRotation.Sectors.shift_point,he] using leftg
  · simpa using positive a
  · have hp := positive (a-1)
    have he : a-1+1=a := by ring
    rw [he] at hp
    have ha : areaDet f.center (f.point a) (f.point (a-1))=
        -areaDet f.center (f.point (a-1)) (f.point a) := by dsimp [areaDet]; ring
    have h5 : a+(5 : ZMod 6)=a-1 := by
      have hh : (5 : ZMod 6)= -1 := by decide
      rw [hh]
      ring
    have hn : -areaDet f.center (f.point (a-1)) (f.point a)<0 := by linarith
    simpa only [UpperOpenMathRotation.Sectors.shift_center,
      UpperOpenMathRotation.Sectors.shift_point,add_zero,h5,ha] using hn

theorem incompatible_partial_triple_fans_card {n r s : ℕ}
    [NeZero (2*r)] [NeZero (2*s)] {L : ℕ → Line ℝ}
    (hr : r=3) (hs : s=3) (hL : NoParallel n L)
    (f : UpperFan.Sectors n r L) (g : UpperFan.Sectors n s L)
    (a : ZMod (2*r)) (b : ZMod (2*s))
    (fselected : a-1∈f.ordinaryShared) (gselected : b-1∈g.ordinaryShared)
    (centerg : g.center=f.point a) (pointg : g.point b=f.center)
    (rightg : g.point (b-1)=f.point (a+1))
    (leftg : g.point (b+1)=f.point (a-1))
    (positive : ∀ z, 0<areaDet f.center (f.point z) (f.point (z+1))) : False := by
  subst r
  subst s
  exact incompatible_partial_triple_fans_at hL f g a b fselected gselected centerg pointg rightg leftg positive

def finite_shared (T : Finset (ZMod 6)) : Finset (ZMod 6) :=
  T.filter (fun z => z-1∈T)

theorem two_one_neighbors_finite (T : Finset (ZMod 6))
    (hcard : (finite_shared T).card=3) (hzero : (0 : ZMod 6)∈finite_shared T)
    (noadjacent : ∀ z∈(finite_shared T).erase 0, z+1∉(finite_shared T).erase 0) :
    (1 : ZMod 6)∈(finite_shared T).erase 0 ∧ (5 : ZMod 6)∈(finite_shared T).erase 0 := by
  have h : ∀ T : Finset (ZMod 6), (finite_shared T).card=3 →
      (0 : ZMod 6)∈finite_shared T →
      (∀ z∈(finite_shared T).erase 0, z+1∉(finite_shared T).erase 0) →
      (1 : ZMod 6)∈(finite_shared T).erase 0 ∧ (5 : ZMod 6)∈(finite_shared T).erase 0 := by
    decide +kernel
  exact h T hcard hzero noadjacent

/-- A triple fan with two ordinary shared rays and just one core-ended
shared ray has its two ordinary shared rays immediately beside that core
ray. This identifies the four-run pattern without assuming a mask. -/
theorem ordinary_neighbors_of_two_one {n : ℕ} {L : ℕ → Line ℝ}
    (f : UpperFan.Sectors n 3 L) (hord : f.ordinaryShared.card=2)
    (hcore : f.coreShared.card=1) (hzero : (0 : ZMod 6)∈f.coreShared) :
    (1 : ZMod 6)∈f.ordinaryShared ∧ (5 : ZMod 6)∈f.ordinaryShared := by
  classical
  have hshared : f.shared.card=3 := by have := f.shared_card_split; omega
  obtain ⟨a,ha⟩ := card_eq_one.mp hcore
  have h0a : (0 : ZMod 6)=a := by simpa only [ha,mem_singleton] using hzero
  have hsingleton : f.coreShared={0} := by simpa only [← h0a] using ha
  have he : f.ordinaryShared=f.shared.erase 0 := by
    ext z
    constructor
    · intro hz
      refine mem_erase.mpr ⟨?_,f.ordinaryShared_subset hz⟩
      intro hz0
      exact (mem_sdiff.mp hzero).2 (hz0 ▸ hz)
    · intro hz
      obtain ⟨hne,hs⟩ := mem_erase.mp hz
      by_contra hnot
      have hc : z∈f.coreShared := mem_sdiff.mpr ⟨hs,hnot⟩
      rw [hsingleton,mem_singleton] at hc
      exact hne hc
  have hsep (z : ZMod 6) (hz : z∈f.ordinaryShared) : z+1∉f.ordinaryShared := by
    intro hn
    obtain ⟨j,hj⟩ := f.no_run (by decide) z
    have hjv : j.val=0 ∨ j.val=1 := by have := j.isLt; omega
    rcases hjv with hjv|hjv
    · simp only [hjv,Nat.cast_zero,add_zero] at hj
      exact hj hz
    · simp only [hjv,Nat.cast_one] at hj
      exact hj hn
  have ht := two_one_neighbors_finite f.triangular hshared (mem_sdiff.mp hzero).1
    (by
      change ∀ z∈f.shared.erase 0, z+1∉f.shared.erase 0
      rw [← he]
      exact hsep)
  change (1 : ZMod 6)∈f.shared.erase 0 ∧ (5 : ZMod 6)∈f.shared.erase 0 at ht
  rw [← he] at ht
  exact ht

theorem ordinary_previous_of_extremal_card {n r : ℕ} [NeZero (2*r)]
    {L : ℕ → Line ℝ} (hr : r=3) (f : UpperFan.Sectors n r L)
    (hcard : 3≤f.ordinaryShared.card) (a : ZMod (2*r))
    (ha : a∈f.coreShared) : a-1∈f.ordinaryShared := by
  subst r
  let g := UpperOpenMathRotation.Sectors.shift f a
  have hg : 3≤g.ordinaryShared.card := by
    rw [UpperOpenMathRotation.Sectors.shift_ordinaryShared_card]
    exact hcard
  have hzero : (0 : ZMod 6)∉g.ordinaryShared := by
    intro h
    have hh := (UpperOpenMathRotation.Sectors.shift_mem_ordinaryShared f a 0).mp h
    exact (mem_sdiff.mp ha).2 (by simpa only [add_zero] using hh)
  have hfive := UpperTripleFan.ordinary_five_of_extremal g hg hzero
  have hmem : (5 : ZMod 6)∈g.ordinaryShared := by
    rw [g.mem_ordinaryShared]
    simp [g.all_sectors_of_extremal (by decide) hg,hfive]
  have hh := (UpperOpenMathRotation.Sectors.shift_mem_ordinaryShared f a 5).mp hmem
  have he : a+(5 : ZMod 6)=a-1 := by
    have h5 : (5 : ZMod 6)= -1 := by decide
    rw [h5]
    ring
  simpa only [he] using hh

theorem ordinary_previous_of_two_one_card {n r : ℕ} [NeZero (2*r)]
    {L : ℕ → Line ℝ} (hr : r=3) (f : UpperFan.Sectors n r L)
    (hord : f.ordinaryShared.card=2) (hcore : f.coreShared.card=1)
    (a : ZMod (2*r)) (ha : a∈f.coreShared) : a-1∈f.ordinaryShared := by
  subst r
  let g := UpperOpenMathRotation.Sectors.shift f a
  have hgo : g.ordinaryShared.card=2 := by
    rw [UpperOpenMathRotation.Sectors.shift_ordinaryShared_card]
    exact hord
  have hgc : g.coreShared.card=1 := by
    rw [UpperOpenMathRotation.Sectors.shift_coreShared_card]
    exact hcore
  have hzero : (0 : ZMod 6)∈g.coreShared := by
    apply (UpperOpenMathRotation.Sectors.shift_mem_coreShared f a 0).mpr
    simpa only [add_zero] using ha
  have hfive := (ordinary_neighbors_of_two_one g hgo hgc hzero).2
  have hh := (UpperOpenMathRotation.Sectors.shift_mem_ordinaryShared f a 5).mp hfive
  have he : a+(5 : ZMod 6)=a-1 := by
    have h5 : (5 : ZMod 6)= -1 := by decide
    rw [h5]
    ring
  simpa only [he] using hh

#print axioms incompatible_partial_triple_fans_at
#print axioms incompatible_partial_triple_fans_card
#print axioms ordinary_neighbors_of_two_one
#print axioms ordinary_previous_of_two_one_card
end Kobon.UpperOpenMathPartialTriple
