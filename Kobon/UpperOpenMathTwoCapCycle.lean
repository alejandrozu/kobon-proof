import Kobon.UpperOpenMathTripleCapBudget
import Kobon.UpperOpenMathSharedMatching

/-!
# Three antipodal two-cap triple fans cannot form a closed core cycle

This closes the local geometric case left by the five-sector antipodal
example: that example exists, but three saturated copies cannot close into
a shared-core triangle. The third core's cap axis would contain two points
lying beyond opposite endpoints of the same core side.
-/
namespace Kobon.UpperOpenMathTwoCapCycle
open Cells FanGeometry UpperFan UpperVertexBudget UpperTriangleIncidence
  UpperSharedIncidence UpperCoreExtraction UpperOpenMathRadialOrder
  UpperOpenMathActualFans UpperOpenMathCapHeavyTriples Finset
open scoped BigOperators

theorem three_two_cap_fans_incompatible {n : ℕ} {L : ℕ → Line ℝ}
    (hL : NoParallel n L) (f g k : UpperFan.Sectors n 3 L)
    (fcap : (3 : ZMod (2*3))∈f.ordinaryShared)
    (gcap : (0 : ZMod (2*3))∈g.ordinaryShared)
    (gcenter : g.center=f.point 1) (gtwo : g.point 2=f.center)
    (gone : g.point 1=k.center) (kcenter : k.center=f.point 2)
    (kzero : k.point 0=f.point 3) (kthree : k.point 3=g.point 0)
    (fnc : f.point 1≠f.center) (knc : ∀ z, k.point z≠k.center) : False := by
  have he32 : (3 : ZMod (2*3))-1=2 := by decide
  have he34 : (3 : ZMod (2*3))+1=4 := by decide
  have he05 : (0 : ZMod (2*3))-1=5 := by decide
  have fV : affineEval (L (f.opposite 3)) k.center=0 := by
    rw [kcenter]
    simpa only [he32] using UpperOpenMathPartialTriple.previous_on_opposite_of_ordinary_shared f 3 fcap
  have fC : affineEval (L (f.opposite 3)) (k.point 0)=0 := by
    rw [kzero]
    exact f.asCyclic.opposite_left 3 (Or.inl fcap)
  have fY : affineEval (L (f.opposite 3)) (f.point 4)=0 := by
    simpa only [UpperFan.Sectors.asCyclic,he34] using f.asCyclic.opposite_right 3 (Or.inl fcap)
  have kB : affineEval (L (k.radial 0)) (k.point 3)=0 := by
    obtain ⟨s,hs,he⟩ := k.antipodal 0
    have he' : k.point 3=(k.center.1-s*((k.point 0).1-k.center.1),
        k.center.2-s*((k.point 0).2-k.center.2)) := by simpa using he
    rw [he',UpperTripleFan.affineEval_antipodal,k.radial_center 0,k.radial_point 0]
    ring
  have gV : affineEval (L (g.opposite 0)) k.center=0 := by
    rw [← gone]
    simpa only [UpperFan.Sectors.asCyclic,zero_add] using g.asCyclic.opposite_right 0 (Or.inl gcap)
  have gB : affineEval (L (g.opposite 0)) (k.point 3)=0 := by
    rw [kthree]
    exact g.asCyclic.opposite_left 0 (Or.inl gcap)
  have gZ : affineEval (L (g.opposite 0)) (g.point 5)=0 := by
    simpa only [he05] using UpperOpenMathPartialTriple.previous_on_opposite_of_ordinary_shared g 0 gcap
  have fAxis : f.opposite 3=k.radial 0 := by
    by_contra hne
    have same := two_lines_two_points (L (f.opposite 3)) (L (k.radial 0))
      k.center (k.point 0)
      (noParallel_any n L hL _ _ (f.opposite 3).isLt (k.radial 0).isLt
        (fun hh => hne (Fin.ext hh))) fV fC (k.radial_center 0) (k.radial_point 0)
    exact knc 0 same.symm
  have gAxis : g.opposite 0=k.radial 0 := by
    by_contra hne
    have same := two_lines_two_points (L (g.opposite 0)) (L (k.radial 0))
      k.center (k.point 3)
      (noParallel_any n L hL _ _ (g.opposite 0).isLt (k.radial 0).isLt
        (fun hh => hne (Fin.ext hh))) gV gB (k.radial_center 0) kB
    exact knc 3 same.symm
  obtain ⟨a,ha,hfa⟩ := f.antipodal 1
  obtain ⟨b,hb,hgb⟩ := g.antipodal 2
  have hfa' : f.point 4=(f.center.1-a*((f.point 1).1-f.center.1),
      f.center.2-a*((f.point 1).2-f.center.2)) := by simpa using hfa
  have hgb' : g.point 5=((f.point 1).1-b*(f.center.1-(f.point 1).1),
      (f.point 1).2-b*(f.center.2-(f.point 1).2)) := by
    simp only [gcenter,gtwo] at hgb
    convert hgb using 1
    congr 1
  have fSideY : affineEval (L (f.radial 1)) (f.point 4)=0 := by
    rw [hfa',UpperTripleFan.affineEval_antipodal,f.radial_center 1,f.radial_point 1]
    ring
  have fSideZ : affineEval (L (f.radial 1)) (g.point 5)=0 := by
    rw [hgb',UpperTripleFan.affineEval_antipodal,f.radial_point 1,f.radial_center 1]
    ring
  have different : f.radial 1≠k.radial 0 := by
    intro he
    have avoid := f.asCyclic.opposite_avoids_center 3 (Or.inl fcap)
    apply avoid
    simpa only [UpperFan.Sectors.asCyclic,fAxis,← he] using f.radial_center 1
  have same : f.point 4=g.point 5 := two_lines_two_points
    (L (f.radial 1)) (L (k.radial 0)) _ _
    (noParallel_any n L hL _ _ (f.radial 1).isLt (k.radial 0).isLt
      (fun hh => different (Fin.ext hh))) fSideY fSideZ
      (by simpa only [fAxis] using fY) (by simpa only [gAxis] using gZ)
  have coords : (f.center.1-a*((f.point 1).1-f.center.1),
      f.center.2-a*((f.point 1).2-f.center.2))=
      ((f.point 1).1-b*(f.center.1-(f.point 1).1),
      (f.point 1).2-b*(f.center.2-(f.point 1).2)) := by rw [← hfa',same,hgb']
  have pos : 0<1+a+b := by linarith
  apply fnc
  apply Prod.ext
  · have hh := congrArg Prod.fst coords
    have hm : (1+a+b)*((f.point 1).1-f.center.1)=0 := by dsimp at hh; nlinarith
    exact sub_eq_zero.mp ((mul_eq_zero.mp hm).resolve_left (ne_of_gt pos))
  · have hh := congrArg Prod.snd coords
    have hm : (1+a+b)*((f.point 1).2-f.center.2)=0 := by dsimp at hh; nlinarith
    exact sub_eq_zero.mp ((mul_eq_zero.mp hm).resolve_left (ne_of_gt pos))

theorem certificate_no_mark {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (triples : ∀ c∈core n L, (supports n L c).card=3)
    (ordinary_two : ∀ c∈core n L, ordinaryDegree n L
      (fun a => ofPredicate n L (tri a) hL (ht a)) c=2)
    (c : Point) (hc : c∈core n L)
    (D : OrderedDirections n L (supports n L c))
    [NeZero (2*(supports n L c).card)] (hr : 2≤(supports n L c).card)
    (z : ZMod (2*(supports n L c).card))
    (hz : z∈(fan n L hL hn tri ht c (UpperOpenMathActualMatching.core_vertex n L hc) D hr).coreShared) :
    ¬(z-1∈(fan n L hL hn tri ht c (UpperOpenMathActualMatching.core_vertex n L hc) D hr).ordinaryShared ∧
      z+1∈(fan n L hL hn tri ht c (UpperOpenMathActualMatching.core_vertex n L hc) D hr).ordinaryShared) := by
  classical
  intro marked
  let f := fan n L hL hn tri ht c (mem_filter.mp hc).1 D hr
  let d := f.point z
  have hd : d∈core n L := fan_core_endpoint n L hL hn tri ht c (mem_filter.mp hc).1 D hr hi hc z hz
  have rd := triples d hd
  letI : NeZero (2*(supports n L d).card) := ⟨by omega⟩
  let E := atPoint n L hL hn d
  let g := fan n L hL hn tri ht d (mem_filter.mp hd).1 E (by omega)
  obtain ⟨w,gcore,gw,right,left⟩ := UpperOpenMathActualMatching.certificate_neighbor_matching
    n L hL hn tri hi ht c d hc hd D E hr (by omega) z hz rfl
  have poor := UpperOpenMathMarkedPoverty.marked_neighbor_poverty_sum_card
    (triples c hc) rd hL f g z w marked.1 marked.2 gcore rfl gw right left
    (fan_positive n L hL hn tri ht c (mem_filter.mp hc).1 D hr)
  have hg : g.ordinaryShared.card=2 := by
    rw [fan_ordinary_card n L hL hn tri ht d (mem_filter.mp hd).1 E (by omega) hi hd]
    exact ordinary_two d hd
  omega

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000 in
theorem finite_two_cap_anchor : ∀ T O : Finset (ZMod 6),
    O⊆UpperOpenMathPartialTriple.finite_shared T → O.card=2 →
    (UpperOpenMathPartialTriple.finite_shared T\O).card=2 →
    (∀ z∈O,z+1∉O) →
    (∀ z∈UpperOpenMathPartialTriple.finite_shared T\O,
      ¬(z-1∈O ∧ z+1∈O)) →
    ∃ a : ZMod 6, a∈O ∧ a+3∈O ∧
      a+1∈UpperOpenMathPartialTriple.finite_shared T\O ∧
      a+2∈UpperOpenMathPartialTriple.finite_shared T\O := by
  decide +kernel

theorem normalized_two_cap_anchor {n : ℕ} {L : ℕ → Line ℝ}
    (f : UpperFan.Sectors n 3 L)
    (ho : f.ordinaryShared.card=2) (hc : f.coreShared.card=2)
    (no_mark : ∀ z∈f.coreShared, ¬(z-1∈f.ordinaryShared ∧ z+1∈f.ordinaryShared)) :
    ∃ a : ZMod (2*3), a∈f.ordinaryShared ∧ a+3∈f.ordinaryShared ∧
      a+1∈f.coreShared ∧ a+2∈f.coreShared := by
  have sep (z : ZMod (2*3)) (hz : z∈f.ordinaryShared) : z+1∉f.ordinaryShared := by
    intro hn
    obtain ⟨j,hj⟩ := f.no_run (by decide) z
    have hjv : j.val=0 ∨ j.val=1 := by have := j.isLt; omega
    rcases hjv with hjv|hjv
    · simp only [hjv,Nat.cast_zero,add_zero] at hj
      exact hj hz
    · simp only [hjv,Nat.cast_one] at hj
      exact hj hn
  exact finite_two_cap_anchor f.triangular f.ordinaryShared f.ordinaryShared_subset ho hc sep no_mark

#print axioms three_two_cap_fans_incompatible
#print axioms certificate_no_mark
#print axioms normalized_two_cap_anchor
end Kobon.UpperOpenMathTwoCapCycle
