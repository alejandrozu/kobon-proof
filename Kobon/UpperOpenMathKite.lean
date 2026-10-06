import Kobon.UpperOpenMathSharedMatching
import Kobon.UpperOpenMathPartialTripleMirror

/-!
# Opposite exterior triangles of a triple-corner kite

Raj Srirangam's `ALL8_NOTE2.md`, section 3, proves that opposite sides of a
kite with four triple corners cannot both have exterior triangular cells.
The local geometric contradiction below checks the antipodal-ray part of
that mechanism. The two exterior-apex equations are explicit matching
interfaces; the actual shared-side extraction is in SharedMatching.
-/
namespace Kobon.UpperOpenMathKite
open Cells FanGeometry UpperFan Finset

theorem six_sub_one : (5 : ZMod (2*3))-1=4 := by decide
theorem six_add_one : (1 : ZMod (2*3))+1=2 := by decide

theorem opposite_exterior_apices_incompatible {n : ℕ} {L : ℕ → Line ℝ}
    (hL : NoParallel n L) (f g k h : UpperFan.Sectors n 3 L)
    (cap : (0 : ZMod 6)∈f.ordinaryShared)
    (gcenter : g.center=f.point 5) (gfive : g.point 5=k.center)
    (hcenter : h.center=f.point 1) (hfive : h.point 5=f.center)
    (kone : k.point 1=g.center)
    (fg_apex : f.point 4=g.point 2) (kh_apex : k.point 4=h.point 2)
    (finj : Function.Injective f.point) (fnc : f.point 1≠f.center) : False := by
  have hfuse : (0 : ZMod 6)∈f.ordinaryShared ∨ 0+1∈f.ordinaryShared := Or.inl cap
  have fprev : affineEval (L (f.opposite 0)) (f.point 5)=0 := by
    have he : (0 : ZMod 6)-1=5 := by decide
    simpa only [he] using UpperOpenMathPartialTriple.previous_on_opposite_of_ordinary_shared f 0 cap
  have fnext : affineEval (L (f.opposite 0)) (f.point 1)=0 := by
    simpa [UpperFan.Sectors.asCyclic] using f.asCyclic.opposite_right 0 hfuse
  have f_rad_opp : f.radial 1≠f.opposite 0 := by
    intro he
    apply f.asCyclic.opposite_avoids_center 0 hfuse
    simpa only [UpperFan.Sectors.asCyclic,← he] using f.radial_center 1
  have distinct : f.radial 1≠g.radial 5 := by
    intro he
    have fp : affineEval (L (f.radial 1)) (f.point 5)=0 := by
      simpa only [he,gcenter] using g.radial_center 5
    have hp := two_lines_two_points (L (f.radial 1)) (L (f.opposite 0))
      (f.point 5) (f.point 1)
      (noParallel_any n L hL _ _ (f.radial 1).isLt (f.opposite 0).isLt
        (fun hh => f_rad_opp (Fin.ext hh))) fp (f.radial_point 1) fprev fnext
    have hz := finj hp
    have hn : (5 : ZMod 6)≠1 := by decide
    exact hn hz
  obtain ⟨a,ha,hfa⟩ := f.antipodal 1
  obtain ⟨b,hb,hgb⟩ := g.antipodal 5
  obtain ⟨c,hc,hkc⟩ := k.antipodal 1
  obtain ⟨d,hd,hhd⟩ := h.antipodal 5
  have hfa' : f.point 4=(f.center.1-a*((f.point 1).1-f.center.1),
      f.center.2-a*((f.point 1).2-f.center.2)) := by simpa using hfa
  have hgb' : g.point 2=(g.center.1-b*((g.point 5).1-g.center.1),
      g.center.2-b*((g.point 5).2-g.center.2)) := by
    convert hgb using 1
    congr 1
  have hkc' : k.point 4=(k.center.1-c*((k.point 1).1-k.center.1),
      k.center.2-c*((k.point 1).2-k.center.2)) := by simpa using hkc
  have hhd' : h.point 2=(h.center.1-d*((h.point 5).1-h.center.1),
      h.center.2-d*((h.point 5).2-h.center.2)) := by
    convert hhd using 1
    congr 1
  have fY : affineEval (L (f.radial 1)) (f.point 4)=0 := by
    rw [hfa',UpperTripleFan.affineEval_antipodal,f.radial_center 1,f.radial_point 1]
    ring
  have gY : affineEval (L (g.radial 5)) (f.point 4)=0 := by
    rw [fg_apex,hgb',UpperTripleFan.affineEval_antipodal,g.radial_center 5,g.radial_point 5]
    ring
  have fZ : affineEval (L (f.radial 1)) (k.point 4)=0 := by
    rw [kh_apex,hhd',hcenter,hfive,UpperTripleFan.affineEval_antipodal,
      f.radial_point 1,f.radial_center 1]
    ring
  have gZ : affineEval (L (g.radial 5)) (k.point 4)=0 := by
    rw [hkc',kone,← gfive,UpperTripleFan.affineEval_antipodal,
      g.radial_point 5,g.radial_center 5]
    ring
  have same : f.point 4=k.point 4 := two_lines_two_points
    (L (f.radial 1)) (L (g.radial 5)) _ _
    (noParallel_any n L hL _ _ (f.radial 1).isLt (g.radial 5).isLt
      (fun hh => distinct (Fin.ext hh))) fY fZ gY gZ
  have coords : (f.center.1-a*((f.point 1).1-f.center.1),
      f.center.2-a*((f.point 1).2-f.center.2))=
      ((f.point 1).1-d*(f.center.1-(f.point 1).1),
      (f.point 1).2-d*(f.center.2-(f.point 1).2)) := by
    rw [← hfa',same,kh_apex,hhd',hcenter,hfive]
  have positive : 0<1+a+d := by linarith
  apply fnc
  apply Prod.ext
  · have hx := congrArg Prod.fst coords
    have hm : (1+a+d)*((f.point 1).1-f.center.1)=0 := by dsimp at hx; nlinarith
    exact sub_eq_zero.mp ((mul_eq_zero.mp hm).resolve_left (ne_of_gt positive))
  · have hy := congrArg Prod.snd coords
    have hm : (1+a+d)*((f.point 1).2-f.center.2)=0 := by dsimp at hy; nlinarith
    exact sub_eq_zero.mp ((mul_eq_zero.mp hm).resolve_left (ne_of_gt positive))

#print axioms opposite_exterior_apices_incompatible

/-- The matching hypotheses of the local kite obstruction follow from the
original certified triangle identities and disjoint interiors. This rules
out simultaneous exterior cells on an opposite pair of kite sides. -/
theorem opposite_shared_kite_sides_incompatible {α : Type*} [Fintype α]
    {n : ℕ} {L : ℕ → Line ℝ} (hL : NoParallel n L)
    (G : α → TriangleGeometry)
    (disjoint : Pairwise (fun a b => Disjoint (G a).interior (G b).interior))
    (f g k h : UpperFan.Sectors n 3 L)
    (cap : (0 : ZMod 6)∈f.ordinaryShared)
    (gcenter : g.center=f.point 5) (gfive : g.point 5=k.center)
    (gone : g.point 1=f.center)
    (hcenter : h.center=f.point 1) (hfive : h.point 5=f.center)
    (hone : h.point 1=k.center) (kone : k.point 1=g.center) (kfive : k.point 5=h.center)
    (fselected : (5 : ZMod 6)∈f.shared) (gselected : (1 : ZMod 6)∈g.shared)
    (kselected : (5 : ZMod 6)∈k.shared) (hselected : (1 : ZMod 6)∈h.shared)
    (finj : Function.Injective f.point) (ginj : Function.Injective g.point)
    (kinj : Function.Injective k.point) (hinj : Function.Injective h.point)
    (fnc : ∀ z, f.point z≠f.center) (gnc : ∀ z, g.point z≠g.center)
    (knc : ∀ z, k.point z≠k.center) (hnc : ∀ z, h.point z≠h.center)
    (fpos : ∀ z, 0<areaDet f.center (f.point z) (f.point (z+1)))
    (gpos : ∀ z, 0<areaDet g.center (g.point z) (g.point (z+1)))
    (kpos : ∀ z, 0<areaDet k.center (k.point z) (k.point (z+1)))
    (hpos : ∀ z, 0<areaDet h.center (h.point z) (h.point (z+1)))
    (factual : ∀ z∈f.triangular, Nonempty
      (UpperOpenMathSectorRecords.Occurrence G f.center f.point z))
    (gactual : ∀ z∈g.triangular, Nonempty
      (UpperOpenMathSectorRecords.Occurrence G g.center g.point z))
    (kactual : ∀ z∈k.triangular, Nonempty
      (UpperOpenMathSectorRecords.Occurrence G k.center k.point z))
    (hactual : ∀ z∈h.triangular, Nonempty
      (UpperOpenMathSectorRecords.Occurrence G h.center h.point z)) : False := by
  classical
  have f4 : (5 : ZMod 6)-1∈f.triangular := (mem_filter.mp fselected).2
  have f5 : (5 : ZMod 6)∈f.triangular := (mem_filter.mp fselected).1
  have g0 : (1 : ZMod 6)-1∈g.triangular := (mem_filter.mp gselected).2
  have g1 : (1 : ZMod 6)∈g.triangular := (mem_filter.mp gselected).1
  have k4 : (5 : ZMod 6)-1∈k.triangular := (mem_filter.mp kselected).2
  have k5 : (5 : ZMod 6)∈k.triangular := (mem_filter.mp kselected).1
  have h0 : (1 : ZMod 6)-1∈h.triangular := (mem_filter.mp hselected).2
  have h1 : (1 : ZMod 6)∈h.triangular := (mem_filter.mp hselected).1
  obtain ⟨fo⟩ := factual _ f4
  obtain ⟨fp⟩ := factual _ f5
  obtain ⟨go⟩ := gactual _ g0
  obtain ⟨gp⟩ := gactual _ g1
  obtain ⟨ko⟩ := kactual _ k4
  obtain ⟨kp⟩ := kactual _ k5
  obtain ⟨ho⟩ := hactual _ h0
  obtain ⟨hp⟩ := hactual _ h1
  have fg := UpperOpenMathFiberMatching.neighboring_points_match G disjoint
    (by decide : 2≤3) (by decide : 2≤3) f.center g.center f.point g.point
    finj ginj fnc gnc fpos gpos 5 1 gcenter gone fo fp go gp
  have kh := UpperOpenMathFiberMatching.neighboring_points_match G disjoint
    (by decide : 2≤3) (by decide : 2≤3) k.center h.center k.point h.point
    kinj hinj knc hnc kpos hpos 5 1 kfive.symm hone ko kp ho hp
  have fg_apex : f.point 4=g.point 2 := by
    simpa only [six_add_one,six_sub_one] using fg.2.symm
  have kh_apex : k.point 4=h.point 2 := by
    simpa only [six_add_one,six_sub_one] using kh.2.symm
  exact opposite_exterior_apices_incompatible hL f g k h cap gcenter gfive hcenter hfive
    kone fg_apex kh_apex finj (fnc 1)

#print axioms opposite_shared_kite_sides_incompatible
end Kobon.UpperOpenMathKite
