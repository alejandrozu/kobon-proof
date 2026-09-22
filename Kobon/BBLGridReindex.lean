import Kobon.BBLGridCuts

/-! Explicit interleaving permutation for the next doubled tangent grid.
This is an ingredient for iteration, not a proof of the invariant itself. -/
namespace Kobon.BBLGridReindex
open Real BBLAnalytic BBLGridCuts

def perm (r j : Nat) : Nat :=
  if j < 4*r then (if j%2=0 then 4*r+j/2 else j/2)
  else (if j%2=0 then j/2 else 4*r+j/2)

def inv (r i : Nat) : Nat :=
  if i < 4*r then (if i < 2*r then 2*i+1 else 2*i)
  else (if i-4*r < 2*r then 2*(i-4*r) else 2*(i-4*r)+1)

theorem perm_bound (r j : Nat) (hj : j < 8*r) : perm r j < 8*r := by
  unfold perm
  split_ifs <;> omega

theorem inv_perm (r j : Nat) (hj : j < 8*r) : inv r (perm r j)=j := by
  unfold perm inv
  split_ifs <;> omega

theorem perm_inv (r i : Nat) (hi : i < 8*r) : perm r (inv r i)=i := by
  unfold perm inv
  split_ifs <;> omega

theorem perm_injective (r : Nat) (i j : Fin (8*r))
    (h : perm r i=perm r j) : i=j := by
  apply Fin.ext
  have hh := congrArg (inv r) h
  simpa only [inv_perm r i i.isLt,inv_perm r j j.isLt] using hh

theorem central_left (r : Nat) (hr : 0 < r) : perm r (4*r-1)=2*r-1 := by
  unfold perm
  split_ifs <;> omega

theorem central_right (r : Nat) (hr : 0 < r) : perm r (4*r)=2*r := by
  unfold perm
  split_ifs <;> omega

theorem rightmost (r : Nat) (hr : 0 < r) : perm r (8*r-1)=8*r-1 := by
  unfold perm
  split_ifs <;> omega

theorem alpha_double (r : Nat) : alpha (2*r)=alpha r/2 := by
  unfold alpha
  push_cast
  ring

theorem next_cut (r : Nat) (ε : ℝ) (j : Int) :
    cut (2*r) ε (2*j+1) = cut r ε (if j < 4*(r:Int) then j else j+1) := by
  unfold cut
  push_cast
  split_ifs <;> try omega
  all_goals congr 1
  all_goals dsimp [leftAngle,rightAngle]
  all_goals rw [alpha_double]
  all_goals push_cast
  all_goals ring

#print axioms perm_injective
#print axioms next_cut
end Kobon.BBLGridReindex
