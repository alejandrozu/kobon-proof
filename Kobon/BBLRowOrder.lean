import Kobon.BBLTriangles

/-! Integer crossing-order model for the BBL auxiliary pencil.

There are `2*h` old non-horizontal lines and `2*h+1` auxiliary lines:
the added lines indexed `0..2*h-1`, and the distinguished horizontal line
indexed `2*h`. The integer keys describe comparisons within a single line.
They are not coordinates and the geometric realization is a separate theorem.
-/
namespace Kobon.BBLRowOrder
set_option maxRecDepth 10000
set_option maxHeartbeats 10000000

def oldKey (j : Int) : Int := 4*j+2

def newKey (h i k : Int) : Int :=
  if i = 2*h then (if k < h then 4*k else 4*k+4)
  else if k = 2*h then (if i < h then 4*i else 4*i+4)
  else if i < h ∧ k < h then
    if i+k < h-1 then 4*(i+k+h)+5
    else if i+k = h-1 then 8*h-1
    else 4*(i+k-h)+1
  else if h ≤ i ∧ h ≤ k then
    if i+k < 3*h-1 then 4*(i+k-h)+7
    else if i+k = 3*h-1 then -1
    else 4*(i+k-3*h)+3
  else if i+k < 2*h-1 then 4*(i+k-h)+3
  else if i+k = 2*h-1 then 4*h
  else 4*(i+k-h)+5

theorem newKey_symm (h i k : Int) (hi : 0 ≤ i) (hi' : i ≤ 2*h)
    (hk : 0 ≤ k) (hk' : k ≤ 2*h) (hne : i ≠ k) :
    newKey h i k = newKey h k i := by
  unfold newKey
  split_ifs <;> omega

theorem key_bounds (h i k : Int) (hh : 1 ≤ h)
    (hi : 0 ≤ i) (hi' : i ≤ 2*h)
    (hk : 0 ≤ k) (hk' : k ≤ 2*h) (hne : i ≠ k) :
    -1 ≤ newKey h i k ∧ newKey h i k ≤ 8*h := by
  unfold newKey
  split_ifs <;> omega

theorem newKey_ne_oldKey (h i k j : Int) : newKey h i k ≠ oldKey j := by
  unfold newKey oldKey
  split_ifs <;> omega

theorem newKey_injective (h i k l : Int) (hh : 1 ≤ h)
    (hi : 0 ≤ i) (hi' : i ≤ 2*h)
    (hk : 0 ≤ k) (hk' : k ≤ 2*h) (hik : i ≠ k)
    (hl : 0 ≤ l) (hl' : l ≤ 2*h) (hil : i ≠ l)
    (heq : newKey h i k = newKey h i l) : k = l := by
  unfold newKey at heq
  split_ifs at heq <;> omega

/-- Every key within distance four of an old crossing is consecutive to it:
no crossing from a different auxiliary line intervenes. -/
theorem auxiliary_outside_of_close (h i k l j : Int) (hh : 1 ≤ h)
    (hi : 0 ≤ i) (hi' : i ≤ 2*h)
    (hk : 0 ≤ k) (hk' : k ≤ 2*h) (hik : i ≠ k)
    (hl : 0 ≤ l) (hl' : l ≤ 2*h) (hil : i ≠ l)
    (hj : 0 ≤ j) (hj' : j < 2*h)
    (hclose : |newKey h i k-oldKey j| < 4) :
    (newKey h i l ≤ newKey h i k ∧ newKey h i l ≤ oldKey j) ∨
    (newKey h i k ≤ newKey h i l ∧ oldKey j ≤ newKey h i l) := by
  rw [abs_lt] at hclose
  unfold newKey oldKey at *
  split_ifs at * <;> omega

theorem old_outside_of_close (h i k j l : Int) (hjl : j ≠ l)
    (hclose : |newKey h i k-oldKey j| < 4) :
    (oldKey l ≤ newKey h i k ∧ oldKey l ≤ oldKey j) ∨
    (newKey h i k ≤ oldKey l ∧ oldKey j ≤ oldKey l) := by
  rw [abs_lt] at hclose
  unfold oldKey at *
  omega

#print axioms newKey_injective
#print axioms auxiliary_outside_of_close
end Kobon.BBLRowOrder
