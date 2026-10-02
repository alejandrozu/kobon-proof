import Kobon.BBLCanonicalPencil
import Kobon.BBLGridReindex

/-! Exact relabeling of a BBL pencil as the next tangent-grid seed. -/
namespace Kobon.BBLRecursiveGrid
open Real Exterior BBLExtrema BBLAnalytic BBLGrid BBLGridCuts
  BBLCrossingCoordinates BBLRealizedPencil BBLCanonicalPencil BBLGridReindex BBLIntersection

def forward (r i : Nat) : Nat := if i=0 then 8*r else perm r (i-1)
def backward (r i : Nat) : Nat := if i=8*r then 0 else inv r i+1

theorem forward_bound (r i : Nat) (hi : i<8*r+1) : forward r i<8*r+1 := by
  unfold forward
  split_ifs with h
  · omega
  · have := perm_bound r (i-1) (by omega)
    omega

theorem backward_bound (r i : Nat) (hi : i<8*r+1) : backward r i<8*r+1 := by
  unfold backward
  split_ifs with h
  · omega
  · unfold inv
    split_ifs <;> omega

theorem forward_backward (r i : Nat) (hi : i<8*r+1) :
    forward r (backward r i)=i := by
  unfold backward
  split_ifs with h
  · simp [forward,h]
  · simp only [forward,Nat.add_eq_zero_iff,one_ne_zero,and_false,if_false,
      Nat.add_sub_cancel]
    exact perm_inv r i (by omega)

theorem backward_forward (r i : Nat) (hi : i<8*r+1) :
    backward r (forward r i)=i := by
  unfold forward
  split_ifs with h
  · simp [backward,h]
  · have hp := perm_bound r (i-1) (by omega)
    simp only [backward,show perm r (i-1)≠8*r by omega,if_false,
      inv_perm r (i-1) (by omega)]
    omega

theorem forward_injective (r : Nat) (i j : Fin (8*r+1))
    (h : forward r i=forward r j) : i=j := by
  apply Fin.ext
  have hh := congrArg (backward r) h
  simpa only [backward_forward r i i.isLt,backward_forward r j j.isLt] using hh

theorem old_intercept_perm (r : Nat) (hr : 5≤r) (ε : ℝ)
    (j : Nat) (hj : j<8*r) :
    oldIntercept (2*r) ε j =
      if perm r j<4*r then oldIntercept r ε (perm r j)
      else newIntercept r (perm r j-4*r) := by
  unfold oldIntercept
  rw [next_cut]
  by_cases hleft : j<4*r
  · have hleftI : (j:Int)<4*(r:Int) := by exact_mod_cast hleft
    rw [if_pos hleftI]
    by_cases he : j%2=0
    · have hp : perm r j=4*r+j/2 := by simp [perm,hleft,he]
      have hb : j/2<2*r := by omega
      rw [hp,if_neg (by omega),Nat.add_sub_cancel_left]
      have hc : (j:Int)=2*((j/2:Nat):Int) := by omega
      rw [hc]
      exact cut_beta_left r hr ε ⟨j/2,by omega⟩ hb
    · have hp : perm r j=j/2 := by simp [perm,hleft,he]
      rw [hp,if_pos (by omega)]
      congr 1
      omega
  · have hleftI : ¬(j:Int)<4*(r:Int) := by omega
    rw [if_neg hleftI]
    by_cases he : j%2=0
    · have hp : perm r j=j/2 := by simp [perm,hleft,he]
      rw [hp,if_pos (by omega)]
      congr 1
      omega
    · have hp : perm r j=4*r+j/2 := by simp [perm,hleft,he]
      have hb : 2*r≤j/2 := by omega
      rw [hp,if_neg (by omega),Nat.add_sub_cancel_left]
      have hc : (j:Int)+1=2*((j/2:Nat):Int)+2 := by omega
      rw [hc]
      exact cut_beta_right r hr ε ⟨j/2,by omega⟩ hb

noncomputable def nextSlopes (r : Nat) (m : Nat→ℝ) (δ κ : ℝ) (j : Nat) : ℝ :=
  if perm r j<4*r then m (perm r j)
  else κ*slopeFactor δ (newIntercept r (perm r j-4*r))

theorem graph_reindex (r : Nat) (hr : 5≤r) (ε : ℝ) (m : Nat→ℝ) (δ κ : ℝ)
    (i : Nat) (hi : i<8*r+1) :
    oldArrangement (2*r) ε (nextSlopes r m δ κ) i =
      arrangement r ε m δ κ (forward r i) := by
  by_cases hz : i=0
  · subst i
    simp only [oldArrangement,if_pos rfl,forward]
    exact (arrangement_zero r ε m δ κ).symm
  · have hb : i-1<8*r := by omega
    have hp := perm_bound r (i-1) hb
    simp only [oldArrangement,hz,if_false,forward]
    rw [old_intercept_perm r hr ε (i-1) hb]
    unfold nextSlopes arrangement
    split_ifs <;> simp_all [pencilLine]

theorem forward_central_left (r : Nat) (hr : 0<r) : forward r (4*r)=2*r-1 := by
  simp only [forward,show 4*r≠0 by omega,if_false,central_left r hr]

theorem forward_central_right (r : Nat) (hr : 0<r) : forward r (4*r+1)=2*r := by
  simp only [forward,show 4*r+1≠0 by omega,if_false,Nat.add_sub_cancel,
    central_right r hr]

#print axioms old_intercept_perm
#print axioms graph_reindex
end Kobon.BBLRecursiveGrid
