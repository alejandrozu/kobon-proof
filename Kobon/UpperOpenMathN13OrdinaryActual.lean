import Kobon.UpperOpenMathN13OrdinaryMiddle
import Kobon.UpperOpenMathN13ExtractionHelpers

/-! The actual ordinary-middle case includes endpoint identification. -/
namespace Kobon.UpperOpenMathN13OrdinaryActual
open Cells FanGeometry UpperFan UpperVertexBudget UpperTriangleIncidence
  UpperCoreExtraction UpperOpenMathAntipodalTwoCapChart
  UpperOpenMathAntipodalAdjacency UpperOpenMathAntipodalFullNeighborPair
  UpperOpenMathAntipodalBalancedAdjacency UpperOpenMathVertexBlocks
  UpperOpenMathSectorRecords Finset
set_option maxHeartbeats 1000000

theorem canonical_ordinary_pair_impossible {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (ht : ∀ a, TrianglePredicate n L (tri a))
    (triples : ∀ p∈core n L, (supports n L p).card=3)
    (f a b : Sectors n 3 L)
    (df : AnyChartData (fun q=>ofPredicate n L (tri q) hL (ht q)) f)
    (ad : AntipodalData (fun q=>ofPredicate n L (tri q) hL (ht q)) a)
    (bd : AntipodalData (fun q=>ofPredicate n L (tri q) hL (ht q)) b)
    (hc : f.center∈core n L) (s0 : (0 : ZMod 6)∈f.triangular)
    (s1 : (1 : ZMod 6)∈f.triangular) (ord : OrdinaryAt n L (f.point 1))
    (acenter : a.center=f.point 0) (bcenter : b.center=f.point 2)
    (w x : ZMod 6) (hw : w∈a.coreShared) (hx : x∈b.coreShared)
    (aback : a.point w=f.center) (bback : b.point x=f.center)
    (aU : a.point (w-1)=f.point 1) (bU : b.point (x+1)=f.point 1) : False := by
  classical
  let G := fun q=>ofPredicate n L (tri q) hL (ht q)
  let Ra := a.point (w-2)
  let Rb := b.point (x+2)
  let axis := f.opposite 0
  have wprev : w-1-1=w-2 := by ring
  have wnext : (w-2)+1=w-1 := by ring
  have xnext : (x+1)+1=x+2 := by ring
  have aOrd : w-1∈a.ordinaryShared := by
    apply (a.mem_ordinaryShared (w-1)).mpr
    refine ⟨by rw [ad.triangular_eq]; simp,by rw [ad.triangular_eq]; simp,?_⟩
    rw [aU]; exact ord
  have bOrd : x+1∈b.ordinaryShared := by
    apply (b.mem_ordinaryShared (x+1)).mpr
    refine ⟨by rw [bd.triangular_eq]; simp,by rw [bd.triangular_eq]; simp,?_⟩
    rw [bU]; exact ord
  have previousRule : ∀ w : ZMod 6, w∈({1,2,4,5} : Finset (ZMod 6)) →
      w-1∈({0,3} : Finset (ZMod 6)) → w-2∈({1,2,4,5} : Finset (ZMod 6)) := by decide
  have nextRule : ∀ x : ZMod 6, x∈({1,2,4,5} : Finset (ZMod 6)) →
      x+1∈({0,3} : Finset (ZMod 6)) → x+2∈({1,2,4,5} : Finset (ZMod 6)) := by decide
  have haR : w-2∈a.coreShared := by
    rw [ad.core_eq]
    rw [ad.core_eq] at hw
    rw [ad.ordinary_eq] at aOrd
    exact previousRule w hw aOrd
  have hbR : x+2∈b.coreShared := by
    rw [bd.core_eq]
    rw [bd.core_eq] at hx
    rw [bd.ordinary_eq] at bOrd
    exact nextRule x hx bOrd
  have RaCore : Ra∈core n L := ad.core_endpoint (w-2) haR
  have RbCore : Rb∈core n L := bd.core_endpoint (x+2) hbR
  have RaVertex : Ra∈vertices n L := (mem_filter.mp RaCore).1
  have RbVertex : Rb∈vertices n L := (mem_filter.mp RbCore).1
  have capEq : f.opposite 0=f.opposite 1 := by
    simpa using cap_eq_selected f 1 (by simpa using s0) s1 ord
  have axisA : affineEval (L axis) a.center=0 := by rw [acenter]; exact cap_left_at f 0 s0
  have axisB : affineEval (L axis) b.center=0 := by
    rw [bcenter]
    change affineEval (L (f.opposite 0)) (f.point 2)=0
    rw [capEq]
    simpa using cap_right_at f 1 s1
  have axisU : affineEval (L axis) (f.point 1)=0 := by simpa using cap_right_at f 0 s0
  have axisC : affineEval (L axis) f.center≠0 := cap_avoids_at f 0 s0
  have ab : a.center≠b.center := by
    intro he
    exact (by decide : (0 : ZMod 6)≠2) (df.injective (acenter.symm.trans (he.trans bcenter)))
  have aBet := ordinary_cap_between a ad.triangular_eq ad.positive (w-1)
    (by rw [aU]; exact ord)
  have bBet := ordinary_cap_between b bd.triangular_eq bd.positive (x+1)
    (by rw [bU]; exact ord)
  obtain ⟨t,ht0,ht1,aEq⟩ := aBet
  obtain ⟨s,hs0,hs1,bEq⟩ := bBet
  simp only [wprev,sub_add_cancel,aU,aback] at aEq
  simp only [add_sub_cancel_right,xnext,bU,bback] at bEq
  change f.point 1=segmentPoint Ra f.center t at aEq
  change f.point 1=segmentPoint f.center Rb s at bEq
  have onRa : affineEval (L (f.radial 1)) Ra=0 := by
    have h := f.radial_point 1
    rw [aEq,affineEval_segment,f.radial_center 1,mul_zero,add_zero] at h
    exact (mul_eq_zero.mp h).resolve_left (by linarith)
  have onRb : affineEval (L (f.radial 1)) Rb=0 := by
    have h := f.radial_point 1
    rw [bEq,affineEval_segment,f.radial_center 1,mul_zero,zero_add] at h
    exact (mul_eq_zero.mp h).resolve_left hs0.ne'
  have relA := axisU
  have relB := axisU
  rw [aEq,affineEval_segment] at relA
  rw [bEq,affineEval_segment] at relB
  have sameSide : 0<affineEval (L axis) Ra*affineEval (L axis) Rb := by
    rcases lt_or_gt_of_ne axisC with negC|posC
    · have posRa : 0<affineEval (L axis) Ra := by
        by_contra h
        have nonpos := mul_nonpos_of_nonneg_of_nonpos (by linarith : 0≤1-t) (le_of_not_gt h)
        have negative := mul_neg_of_pos_of_neg ht0 negC
        linarith
      have posRb : 0<affineEval (L axis) Rb := by
        by_contra h
        have nonpos := mul_nonpos_of_nonneg_of_nonpos hs0.le (le_of_not_gt h)
        have negative := mul_neg_of_pos_of_neg (by linarith : 0<1-s) negC
        linarith
      exact mul_pos posRa posRb
    · have negRa : affineEval (L axis) Ra<0 := by
        by_contra h
        have nonneg := mul_nonneg (by linarith : 0≤1-t) (le_of_not_gt h)
        have positive := mul_pos ht0 posC
        linarith
      have negRb : affineEval (L axis) Rb<0 := by
        by_contra h
        have nonneg := mul_nonneg hs0.le (le_of_not_gt h)
        have positive := mul_pos (by linarith : 0<1-s) posC
        linarith
      exact mul_pos_of_neg_of_neg negRa negRb
  have capUsed (g : Sectors n 3 L) (gd : AntipodalData G g) (z : ZMod 6) :
      {g.point z,g.point (z+1)}∈usedEdges G := by
    obtain ⟨o⟩ := gd.occurrences z (by rw [gd.triangular_eq]; simp)
    have h := transported_side_used G o.index o.triangle o.transport 1
    change ({o.triangle.q,o.triangle.r} : Edge)∈usedEdges G at h
    rw [o.left,o.right] at h
    exact h
  have usedA : {f.point 1,Ra}∈usedEdges G := by
    simpa only [wnext,aU,pair_comm] using capUsed a ad (w-2)
  have usedB : {f.point 1,Rb}∈usedEdges G := by
    simpa only [xnext,bU] using capUsed b bd (x+1)
  have equal := UpperOpenMathN13ExtractionHelpers.certificate_same_side_used_endpoints_unique
    n L hL hn tri ht (f.radial 1) (f.point 1) Ra Rb (f.radial_point 1) onRa onRb
    RaVertex RbVertex (L axis) axisU sameSide usedA usedB
  exact UpperOpenMathN13OrdinaryMiddle.ordinary_middle_pair_impossible n L hL G a b ad bd
    f.center (f.point 1) Ra w x aback bback aU bU rfl (by exact equal.symm)
    ord (triples f.center hc) (triples Ra RaCore) axis axisA axisB axisU axisC ab

#print axioms canonical_ordinary_pair_impossible
end Kobon.UpperOpenMathN13OrdinaryActual
