import Kobon.UpperFanSupport

/-!
# Adjacent extremal triple fans: a local incompatibility

The interface specifies the common elementary edge and its two incident
triangular cells by matching their endpoints in two consistently indexed
six-sector fans. It does not assume a global extraction of those data.
-/
namespace Kobon.UpperTripleFan
open Cells FanGeometry UpperFan Finset

@[simp] theorem five_add_one : (5 : ZMod 6)+1=0 := by decide
@[simp] theorem five_sub_one : (5 : ZMod 6)-1=4 := by decide
@[simp] theorem one_add_three : (1 : ZMod 6)+3=4 := by decide

theorem affineEval_antipodal (l : Line ℝ) (c p : Point) (v : ℝ) :
    affineEval l (c.1-v*(p.1-c.1),c.2-v*(p.2-c.2))=
      (1+v)*affineEval l c-v*affineEval l p := by
  dsimp [affineEval]
  ring

theorem previous_point_on_opposite {n r : ℕ} [NeZero (2*r)]
    {L : ℕ → Line ℝ} (f : UpperFan.Sectors n r L)
    (hall : f.triangular=univ) (z : ZMod (2*r))
    (ho : OrdinaryAt n L (f.point z)) :
    affineEval (L (f.opposite z)) (f.point (z-1))=0 := by
  have hz : z∈f.ordinaryShared := by
    rw [f.mem_ordinaryShared]
    simp only [hall,mem_univ,true_and]
    exact ho
  have hp : z-1∈f.ordinaryShared ∨ z-1+1∈f.ordinaryShared := by
    right
    simpa using hz
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

/-- A full six-sector fan has only two alternating maximum independent sets
of ordinary rays. This finite lemma checks their needed local consequence. -/
theorem neighboring_selected (S : Finset (ZMod 6)) (hcard : S.card=3)
    (hsep : ∀ z∈S, z+1∉S) (hzero : (0 : ZMod 6)∉S) :
    (5 : ZMod 6)∈S := by
  have h : ∀ S : Finset (ZMod 6), S.card=3 →
      (∀ z∈S, z+1∉S) → (0 : ZMod 6)∉S → (5 : ZMod 6)∈S := by
    decide +kernel
  exact h S hcard hsep hzero

/-- Two full triple fans with an ordinary neighboring endpoint on each side
cannot be matched across their common edge. This is a geometric obstruction,
not a graph-theoretic assumption. -/
theorem incompatible_full_triple_fans {n : ℕ} {L : ℕ → Line ℝ}
    (hL : NoParallel n L) (f g : UpperFan.Sectors n 3 L)
    (hf : f.triangular=univ) (hg : g.triangular=univ)
    (ofive : OrdinaryAt n L (f.point 5))
    (gfive : OrdinaryAt n L (g.point 5))
    (centerg : g.center=f.point 0) (pointg : g.point 0=f.center)
    (rightg : g.point 5=f.point 1) (leftg : g.point 1=f.point 5)
    (pos : 0<areaDet f.center (f.point 0) (f.point 1))
    (neg : areaDet f.center (f.point 0) (f.point 5)<0) : False := by
  have hfs : (5 : ZMod 6)∈f.ordinaryShared := by
    rw [f.mem_ordinaryShared]
    simp [hf,ofive]
  have hgs : (5 : ZMod 6)∈g.ordinaryShared := by
    rw [g.mem_ordinaryShared]
    simp [hg,gfive]
  have hfuse : (5 : ZMod 6)∈f.ordinaryShared ∨ 5+1∈f.ordinaryShared := Or.inl hfs
  have hguse : (5 : ZMod 6)∈g.ordinaryShared ∨ 5+1∈g.ordinaryShared := Or.inl hgs
  have fS : affineEval (L (f.opposite 5)) (f.point 5)=0 :=
    f.asCyclic.opposite_left 5 hfuse
  have fQ : affineEval (L (f.opposite 5)) (f.point 0)=0 := by
    simpa [UpperFan.Sectors.asCyclic] using f.asCyclic.opposite_right 5 hfuse
  have fB : affineEval (L (f.opposite 5)) (f.point 4)=0 := by
    simpa using previous_point_on_opposite f hf 5 ofive
  have gR : affineEval (L (g.opposite 5)) (f.point 1)=0 := by
    simpa [UpperFan.Sectors.asCyclic,rightg] using g.asCyclic.opposite_left 5 hguse
  have gP : affineEval (L (g.opposite 5)) f.center=0 := by
    have hh := g.asCyclic.opposite_right 5 hguse
    simpa [UpperFan.Sectors.asCyclic,pointg] using hh
  have gD : affineEval (L (g.opposite 5)) (g.point 4)=0 := by
    simpa using previous_point_on_opposite g hg 5 gfive
  obtain ⟨b,hb,hB⟩ := f.antipodal 1
  obtain ⟨d,hd,hD⟩ := g.antipodal 1
  have hB' : f.point 4=(f.center.1-b*((f.point 1).1-f.center.1),
      f.center.2-b*((f.point 1).2-f.center.2)) := by simpa using hB
  have hD' : g.point 4=((f.point 0).1-d*((f.point 5).1-(f.point 0).1),
      (f.point 0).2-d*((f.point 5).2-(f.point 0).2)) := by
    simpa [centerg,leftg] using hD
  have gB : affineEval (L (g.opposite 5)) (f.point 4)=0 := by
    rw [hB',affineEval_antipodal,gP,gR]
    ring
  have fD : affineEval (L (f.opposite 5)) (g.point 4)=0 := by
    rw [hD',affineEval_antipodal,fQ,fS]
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
      -b*areaDet f.center (f.point 0) (f.point 1) := by
    rw [hB']
    dsimp [areaDet]
    ring
  have hareaD : areaDet f.center (f.point 0) (g.point 4)=
      -d*areaDet f.center (f.point 0) (f.point 5) := by
    rw [hD']
    dsimp [areaDet]
    ring
  rw [hBD,hareaD] at hareaB
  have hbp := mul_pos hb pos
  have hdn := mul_neg_of_pos_of_neg hd neg
  nlinarith

/-- For an extremal triple fan, either neighbor of a core-ended shared ray
is ordinary. Here the common ray is normalized to index zero. -/
theorem ordinary_five_of_extremal {n : ℕ} {L : ℕ → Line ℝ}
    (f : UpperFan.Sectors n 3 L) (hcard : 3≤f.ordinaryShared.card)
    (hzero : (0 : ZMod 6)∉f.ordinaryShared) :
    OrdinaryAt n L (f.point 5) := by
  have hc : f.ordinaryShared.card=3 := by
    have hh := f.ordinary_shared_card_le (by decide)
    omega
  have hsep (z : ZMod 6) (hz : z∈f.ordinaryShared) : z+1∉f.ordinaryShared := by
    intro hn
    obtain ⟨j,hj⟩ := f.no_run (by decide) z
    have hjv : j.val=0 ∨ j.val=1 := by have := j.isLt; omega
    rcases hjv with hjv|hjv
    · simp only [hjv,Nat.cast_zero,add_zero] at hj
      exact hj hz
    · simp only [hjv,Nat.cast_one] at hj
      exact hj hn
  have hh := neighboring_selected f.ordinaryShared hc hsep hzero
  exact ((f.mem_ordinaryShared 5).mp hh).2.2

/-- Extremal triple cores cannot be adjacent across a consistently extracted
shared edge with its two incident triangular cells. The matching equations
are explicit, so no global adjacency extraction is hidden in the theorem. -/
theorem extremal_triple_fans_not_adjacent {n : ℕ} {L : ℕ → Line ℝ}
    (hL : NoParallel n L) (f g : UpperFan.Sectors n 3 L)
    (hf : 3≤f.ordinaryShared.card) (hg : 3≤g.ordinaryShared.card)
    (fcore : (0 : ZMod 6)∉f.ordinaryShared)
    (gcore : (0 : ZMod 6)∉g.ordinaryShared)
    (centerg : g.center=f.point 0) (pointg : g.point 0=f.center)
    (rightg : g.point 5=f.point 1) (leftg : g.point 1=f.point 5)
    (positive : ∀ z, 0<areaDet f.center (f.point z) (f.point (z+1))) : False := by
  apply incompatible_full_triple_fans hL f g
    (f.all_sectors_of_extremal (by decide) hf)
    (g.all_sectors_of_extremal (by decide) hg)
    (ordinary_five_of_extremal f hf fcore)
    (ordinary_five_of_extremal g hg gcore)
    centerg pointg rightg leftg
  · simpa using positive 0
  · have hpos : 0<areaDet f.center (f.point 5) (f.point 0) := by
      simpa using positive 5
    have hswap : areaDet f.center (f.point 5) (f.point 0)=
        -areaDet f.center (f.point 0) (f.point 5) := by dsimp [areaDet]; ring
    rw [hswap] at hpos
    linarith

#print axioms neighboring_selected
#print axioms incompatible_full_triple_fans
#print axioms extremal_triple_fans_not_adjacent
end Kobon.UpperTripleFan

