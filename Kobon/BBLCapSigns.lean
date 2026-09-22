import Kobon.BBLCaps

/-! Orientation data for the cap rows, expressed in the integer model.
This identifies when an auxiliary crossing separates a cap endpoint from
the cap line's horizontal-axis intersection. The next geometric step may
combine this with the signs of the auxiliary slopes and ordered intercepts.
-/
namespace Kobon.BBLCapSigns
open BBLRowOrder BBLCaps
set_option maxRecDepth 10000
set_option maxHeartbeats 10000000

def horizontalKey (r i : Nat) : Int := if i<2*r then 4*(i:Int) else 4*(i:Int)+4

def positiveAtHorizontal (r i k : Nat) : Prop :=
  (k < 2*r ∧ i < k) ∨ (2*r ≤ k ∧ k < i)

def keyOutside (z a b : Int) : Prop := (z≤a ∧ z≤b) ∨ (a≤z ∧ b≤z)

theorem horizontalKey_eq (r i : Nat) (hi : i<4*r) :
    newKey (2*r) i (4*r)=horizontalKey r i := by
  unfold newKey horizontalKey
  push_cast
  split_ifs <;> omega

theorem cap_key_signs (r j k : Nat) (hr : 1≤r) (hj : j<4*r-1)
    (hc : j≠2*r-1) (hk : k<4*r) (hki : k≠capRow r j) :
    keyOutside (newKey (2*r) (capRow r j) k) (oldKey j)
      (horizontalKey r (capRow r j)) ↔
      (j%2=0 ↔ positiveAtHorizontal r (capRow r j) k) := by
  unfold capRow at *
  split_ifs at * <;> unfold keyOutside horizontalKey positiveAtHorizontal newKey oldKey <;>
    push_cast <;> split_ifs <;> omega

#print axioms cap_key_signs
end Kobon.BBLCapSigns
