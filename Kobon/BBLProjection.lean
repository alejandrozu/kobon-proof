import Kobon.BBLRowGeometry
import Kobon.BBLRealizedPencil

/-! Transfer the actual crossing order from x to an admissible oblique
projection whenever that projection increases on each auxiliary graph line. -/
namespace Kobon.BBLProjection
open Exterior BBLExtrema BBLRowGeometry BBLRealizedPencil BBLRealization
set_option autoImplicit false

theorem graph_projection_mono (m a : ℝ) (w : Line ℝ) (p q : Point)
    (hp : affineEval (graphLine m a) p=0) (hq : affineEval (graphLine m a) q=0)
    (hw : 0≤w.a+w.b*m) (h : p.1≤q.1) : projection w p≤projection w q := by
  have heq : projection w q-projection w p=(w.a+w.b*m)*(q.1-p.1) := by
    dsimp only [affineEval,graphLine,projection] at hp hq ⊢
    linear_combination w.b*hp-w.b*hq
  have hh := mul_nonneg hw (sub_nonneg.mpr h)
  linarith

theorem graph_projection_strict_mono (m a : ℝ) (w : Line ℝ) (p q : Point)
    (hp : affineEval (graphLine m a) p=0) (hq : affineEval (graphLine m a) q=0)
    (hw : 0<w.a+w.b*m) (h : p.1<q.1) : projection w p<projection w q := by
  have heq : projection w q-projection w p=(w.a+w.b*m)*(q.1-p.1) := by
    dsimp only [affineEval,graphLine,projection] at hp hq ⊢
    linear_combination w.b*hp-w.b*hq
  have hh := mul_pos hw (sub_pos.mpr h)
  linarith

theorem crossing_order_transfer (r : Nat) (L : Nat → Line ℝ) (w : Line ℝ)
    (hp : NoParallel (8*r+1) L)
    (m a : Nat → ℝ)
    (hgraph : ∀ i, i≤4*r → L (4*r+i)=graphLine (m i) (a i))
    (hpositive : ∀ i, i≤4*r → 0≤w.a+w.b*m i)
    (horder : CrossingOrder r L xDirection) : CrossingOrder r L w := by
  intro i hi b c hb hc hbc
  have hrow : 4*r+i<8*r+1 := by omega
  have hpb := det_ne_of_ne (8*r+1) L hp ⟨4*r+i,hrow⟩ b (by
    intro he
    exact hb (congrArg Fin.val he).symm)
  have hpc := det_ne_of_ne (8*r+1) L hp ⟨4*r+i,hrow⟩ c (by
    intro he
    exact hc (congrArg Fin.val he).symm)
  have hab := intersection_on_left (L (4*r+i)) (L b) hpb
  have hac := intersection_on_left (L (4*r+i)) (L c) hpc
  rw [hgraph i hi] at hab hac ⊢
  apply graph_projection_mono (m i) (a i) w _ _ hab hac (hpositive i hi)
  simpa only [projection,xDirection,one_mul,zero_mul,add_zero,hgraph i hi]
    using horder i hi b c hb hc hbc

#print axioms crossing_order_transfer
end Kobon.BBLProjection
