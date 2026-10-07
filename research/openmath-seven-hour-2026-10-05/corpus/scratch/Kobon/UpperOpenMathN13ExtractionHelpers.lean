import Kobon.UpperOpenMathAnyChartMatching
import Kobon.UpperOpenMathCommonNeighbor

/-! Small actual extraction helpers for the remaining N13 cap cases. -/
namespace Kobon.UpperOpenMathN13ExtractionHelpers
open Cells FanGeometry UpperFan UpperVertexBudget UpperTriangleIncidence
  UpperCoreExtraction UpperOpenMathAntipodalTwoCapChart
  UpperOpenMathCommonNeighbor Finset
set_option maxHeartbeats 1000000

theorem antipodal_previous_ordinary {α : Type*} [Fintype α]
    {n : ℕ} {L : ℕ → Line ℝ} (G : α → TriangleGeometry)
    (g : Sectors n 3 L) (dg : AntipodalData G g)
    (w : ZMod 6) (hw : w∈g.coreShared)
    (prevTriple : (supports n L (g.point (w-1))).card=3) :
    OrdinaryAt n L (g.point (w-2)) := by
  classical
  have hc : w-1∈g.coreShared := by
    apply mem_sdiff.mpr
    refine ⟨by simp [Sectors.shared,dg.triangular_eq],?_⟩
    intro ho
    have hOrd := ((g.mem_ordinaryShared (w-1)).mp ho).2.2
    have h2 := (ordinary_iff_support_card n L (g.point (w-1))).mp hOrd
    omega
  have finiteRule : ∀ w : ZMod 6,
      w∈({1,2,4,5} : Finset (ZMod 6)) → w-1∈({1,2,4,5} : Finset (ZMod 6)) →
      w-2∈({0,3} : Finset (ZMod 6)) := by decide
  have ho : w-2∈g.ordinaryShared := by
    rw [dg.ordinary_eq]
    rw [dg.core_eq] at hw hc
    exact finiteRule w hw hc
  exact ((g.mem_ordinaryShared (w-2)).mp ho).2.2

theorem antipodal_next_ordinary {α : Type*} [Fintype α]
    {n : ℕ} {L : ℕ → Line ℝ} (G : α → TriangleGeometry)
    (g : Sectors n 3 L) (dg : AntipodalData G g)
    (w : ZMod 6) (hw : w∈g.coreShared)
    (nextTriple : (supports n L (g.point (w+1))).card=3) :
    OrdinaryAt n L (g.point (w+2)) := by
  classical
  have hc : w+1∈g.coreShared := by
    apply mem_sdiff.mpr
    refine ⟨by simp [Sectors.shared,dg.triangular_eq],?_⟩
    intro ho
    have hOrd := ((g.mem_ordinaryShared (w+1)).mp ho).2.2
    have h2 := (ordinary_iff_support_card n L (g.point (w+1))).mp hOrd
    omega
  have finiteRule : ∀ w : ZMod 6,
      w∈({1,2,4,5} : Finset (ZMod 6)) → w+1∈({1,2,4,5} : Finset (ZMod 6)) →
      w+2∈({0,3} : Finset (ZMod 6)) := by decide
  have ho : w+2∈g.ordinaryShared := by
    rw [dg.ordinary_eq]
    rw [dg.core_eq] at hw hc
    exact finiteRule w hw hc
  exact ((g.mem_ordinaryShared (w+2)).mp ho).2.2

theorem certificate_same_side_used_endpoints_unique {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (ht : ∀ a, TrianglePredicate n L (tri a))
    (i : Fin n) (c p q : Point)
    (hc : affineEval (L i) c=0) (hp : affineEval (L i) p=0)
    (hq : affineEval (L i) q=0) (vp : p∈vertices n L) (vq : q∈vertices n L)
    (w : Line ℝ) (wc : affineEval w c=0)
    (same : 0<affineEval w p*affineEval w q)
    (cp : {c,p}∈usedEdges (fun a=>ofPredicate n L (tri a) hL (ht a)))
    (cq : {c,q}∈usedEdges (fun a=>ofPredicate n L (tri a) hL (ht a))) : p=q := by
  by_contra ne
  obtain ⟨t,ht0,ht1,ceq⟩ := certificate_common_used_center_between n L hL hn tri ht
    i c p q hc hp hq vp vq ne cp cq
  have h := wc
  rw [ceq,affineEval_segment] at h
  rcases mul_pos_iff.mp same with ⟨posP,posQ⟩|⟨negP,negQ⟩
  · have left := mul_pos (by linarith : 0<1-t) posP
    have right := mul_pos ht0 posQ
    linarith
  · have left := mul_neg_of_pos_of_neg (by linarith : 0<1-t) negP
    have right := mul_neg_of_pos_of_neg ht0 negQ
    linarith

#print axioms antipodal_previous_ordinary
#print axioms antipodal_next_ordinary
#print axioms certificate_same_side_used_endpoints_unique
end Kobon.UpperOpenMathN13ExtractionHelpers
