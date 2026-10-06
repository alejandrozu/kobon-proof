import Kobon.OpenMathBoundarySectorGeometry
import Mathlib.Data.Fintype.BigOperators
namespace Kobon.OpenMathBoundarySignedSamples
open Exterior OpenMathBoundaryNormals OpenMathBoundarySectors OpenMathBoundarySectorGeometry Finset
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1000000

def signedNormal (w : Line ℝ) (b : Bool) : Line ℝ :=
  if b then ⟨-w.a,-w.b,0⟩ else w

theorem projection_signed (w : Line ℝ) (b : Bool) (p : Point) :
    projection (signedNormal w b) p=signedValue b (projection w p) := by
  cases b <;> simp [signedNormal,signedValue,projection] <;> ring

theorem signed_admissible (n : Nat) (L : Nat→Line ℝ) (w : Line ℝ)
    (hw : Admissible n L w) (b : Bool) : Admissible n L (signedNormal w b) := by
  intro i
  cases b
  · exact hw i
  · have hh : det (L i) (signedNormal w true)= -det (L i) w := by
      dsimp [signedNormal,det]
      ring
    rw [hh]
    exact neg_ne_zero.mpr (hw i)

noncomputable def normal (n : Nat) (L : Nat→Line ℝ) (hp : NoParallel n L)
    (hn : 2≤n) (a : Fin n × Bool) : Line ℝ :=
  signedNormal (normalAt (L 0) ((samples n L hp hn).sample a.1)) a.2

theorem normal_admissible (n : Nat) (L : Nat→Line ℝ) (hp : NoParallel n L)
    (hn : 2≤n) (a : Fin n × Bool) : Admissible n L (normal n L hp hn a) :=
  signed_admissible n L _ (sample_admissible n L hp hn a.1) a.2

theorem choiceCount_sum (a b : ℝ) :
    (∑ s : Bool, if 0<signedValue s a ∧ 0<signedValue s b then (1 : Nat) else 0)=
      choiceCount a b := by
  classical
  rw [choiceCount_formula,Fintype.sum_bool]
  simp only [signedValue,Bool.false_eq_true,if_false,if_true,neg_pos]
  omega

theorem pair_signed_sector_count (n : Nat) (L : Nat→Line ℝ) (hp : NoParallel n L)
    (hn : 2≤n) (i j : Fin n) (hij : i<j) (p q : Point)
    (hpn : p≠(0,0)) (hqn : q≠(0,0))
    (hpi : projection (L i) p=0) (hqj : projection (L j) q=0)
    (hc : ∀ r : Fin n, r≠i → r≠j → 0<projection (L r) p*projection (L r) q) :
    (∑ a : Fin n × Bool, if 0<projection (normal n L hp hn a) p ∧
      0<projection (normal n L hp hn a) q then (1 : Nat) else 0)=n-1 := by
  classical
  rw [Fintype.sum_prod_type]
  simp only [normal,projection_signed,choiceCount_sum]
  exact pair_sector_count n L hp hn i j hij p q hpn hqn hpi hqj hc

#print axioms normal_admissible
#print axioms pair_signed_sector_count
end Kobon.OpenMathBoundarySignedSamples
