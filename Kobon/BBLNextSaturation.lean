import Kobon.BBLGridReindex
import Kobon.BBLRowGeometry

/-! Every consecutive pair in the next sorted grid supports a triangle on Y0.
The statement retains the canonical labels; transporting the whole witness
list to the next iteration is deliberately a separate obligation. -/
namespace Kobon.BBLNextSaturation
open BBLGridReindex BBLRowOrder BBLCount BBLRowGeometry Exterior
set_option maxRecDepth 10000
set_option maxHeartbeats 10000000

def gapTriangle (r j : Nat) : Triple :=
  ⟨min (perm r j) (perm r (j+1)),max (perm r j) (perm r (j+1)),8*r⟩

theorem noncentral_gap (r j : Nat) (hr : 1≤r) (hj : j<8*r-1) (hc : j≠4*r-1) :
    ∃ o i : Nat, o<4*r ∧ i<4*r ∧
      |newKey (2*r) i (4*r)-oldKey o|<4 ∧
      gapTriangle r j=mixedTriangle r (i,4*r,o) := by
  let a := min (perm r j) (perm r (j+1))
  let b := max (perm r j) (perm r (j+1))
  have hb : a<4*r ∧ 4*r≤b ∧ b<8*r := by
    dsimp [a,b]
    unfold perm
    split_ifs <;> omega
  have hkey : newKey (2*r) (b-4*r) (4*r)=
      if (b:Int)-4*r<2*r then 4*((b:Int)-4*r) else 4*((b:Int)-4*r)+4 := by
    unfold newKey
    rw [if_neg (by omega),if_pos (by ring)]
  have hclose : |newKey (2*r) (b-4*r) (4*r)-oldKey a|<4 := by
    rw [hkey]
    dsimp [a,b]
    unfold perm oldKey
    simp only [abs_lt]
    split_ifs <;> omega
  refine ⟨a,b-4*r,hb.1,by omega,?_,?_⟩
  · convert hclose using 1 <;> congr 3 <;> omega
  unfold gapTriangle mixedTriangle
  change Triple.mk a b (8*r)=Triple.mk a (4*r+(b-4*r)) (4*r+4*r)
  congr 1 <;> omega

theorem next_saturated (r : Nat) (hr : 1≤r) (L : Nat → Line ℝ) (w : Line ℝ)
    (hp : NoParallel (8*r+1) L) (hs : NoConcurrent (8*r+1) L)
    (hw : Admissible (8*r+1) L w) (ho : CrossingOrder r L w)
    (hcenter : TrianglePredicate (8*r+1) L ⟨2*r-1,2*r,8*r⟩) :
    ∀ j, j<8*r-1 → TrianglePredicate (8*r+1) L (gapTriangle r j) := by
  intro j hj
  by_cases hc : j=4*r-1
  · subst j
    have hid : 4*r-1+1=4*r := by omega
    simpa only [gapTriangle,hid,central_left r (by omega),central_right r (by omega),
      Nat.min_eq_left (show 2*r-1≤2*r by omega),
      Nat.max_eq_right (show 2*r-1≤2*r by omega)] using hcenter
  · obtain ⟨o,i,ho',hi,hclose,hgap⟩ := noncentral_gap r j hr hj hc
    rw [hgap]
    apply mixed_triangle r hr L w hp hs hw ho (i,4*r,o)
    exact (mem_mixed r i (4*r) o).mpr ⟨hi,le_rfl,ho',hclose⟩

#print axioms next_saturated
end Kobon.BBLNextSaturation
