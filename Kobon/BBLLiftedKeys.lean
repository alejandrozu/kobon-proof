import Kobon.BBLRowOrder

/-! The negative complementary crossing is beyond every finite reference cut.
Raising its key by two preserves the order in each auxiliary row. -/
namespace Kobon.BBLLiftedKeys
open BBLRowOrder
set_option maxRecDepth 10000
set_option maxHeartbeats 10000000

def NegativeComplement (h i k : Int) : Prop :=
  i < h ∧ k < h ∧ i+k = h-1

instance (h i k : Int) : Decidable (NegativeComplement h i k) :=
  inferInstanceAs (Decidable (i < h ∧ k < h ∧ i+k = h-1))

def liftedNewKey (h i k : Int) : Int :=
  if NegativeComplement h i k then 8*h+1 else newKey h i k

theorem complement_key (h i k : Int) (hh : 1 ≤ h)
    (hi : 0 ≤ i) (hk : 0 ≤ k) (hc : NegativeComplement h i k) :
    newKey h i k = 8*h-1 := by
  unfold NegativeComplement at hc
  unfold newKey
  split_ifs <;> omega

theorem complement_row_bound (h i k l : Int) (hh : 1 ≤ h)
    (hi : 0 ≤ i) (hk : 0 ≤ k) (hc : NegativeComplement h i k)
    (hl : 0 ≤ l) (hl' : l ≤ 2*h) (hil : i ≠ l) :
    newKey h i l ≤ 8*h-1 := by
  unfold NegativeComplement at hc
  unfold newKey
  split_ifs <;> omega

theorem complement_row_strict (h i k l : Int) (hh : 1 ≤ h)
    (hi : 0 ≤ i) (hi' : i ≤ 2*h)
    (hk : 0 ≤ k) (hk' : k ≤ 2*h) (hik : i ≠ k)
    (hl : 0 ≤ l) (hl' : l ≤ 2*h) (hil : i ≠ l)
    (hc : NegativeComplement h i k) (hn : ¬NegativeComplement h i l) :
    newKey h i l < 8*h-1 := by
  have hb := complement_row_bound h i k l hh hi hk hc hl hl' hil
  have he := complement_key h i k hh hi hk hc
  have hnkl : k ≠ l := by intro heq; subst l; exact hn hc
  have hne : newKey h i k ≠ newKey h i l := by
    intro heq
    exact hnkl (newKey_injective h i k l hh hi hi' hk hk' hik hl hl' hil heq)
  omega

theorem lifted_new_le_iff (h i k l : Int) (hh : 1 ≤ h)
    (hi : 0 ≤ i) (hi' : i ≤ 2*h)
    (hk : 0 ≤ k) (hk' : k ≤ 2*h) (hik : i ≠ k)
    (hl : 0 ≤ l) (hl' : l ≤ 2*h) (hil : i ≠ l) :
    liftedNewKey h i k ≤ liftedNewKey h i l ↔ newKey h i k ≤ newKey h i l := by
  by_cases hck : NegativeComplement h i k
  · have hek := complement_key h i k hh hi hk hck
    by_cases hcl : NegativeComplement h i l
    · have hel := complement_key h i l hh hi hl hcl
      simp [liftedNewKey,hck,hcl,hek,hel]
    · have hlt := complement_row_strict h i k l hh hi hi' hk hk' hik hl hl' hil hck hcl
      simp only [liftedNewKey,if_pos hck,if_neg hcl]
      omega
  · by_cases hcl : NegativeComplement h i l
    · have hel := complement_key h i l hh hi hl hcl
      have hlt := complement_row_strict h i l k hh hi hi' hl hl' hil hk hk' hik hcl hck
      simp only [liftedNewKey,if_neg hck,if_pos hcl]
      omega
    · simp [liftedNewKey,hck,hcl]

theorem lifted_old_le_iff (h i k j : Int) (hh : 1 ≤ h)
    (hi : 0 ≤ i) (hk : 0 ≤ k) (hj : 0 ≤ j) (hj' : j < 2*h) :
    oldKey j ≤ liftedNewKey h i k ↔ oldKey j ≤ newKey h i k := by
  by_cases hc : NegativeComplement h i k
  · have he := complement_key h i k hh hi hk hc
    simp only [liftedNewKey,if_pos hc,oldKey]
    omega
  · simp [liftedNewKey,hc]

theorem lifted_le_old_iff (h i k j : Int) (hh : 1 ≤ h)
    (hi : 0 ≤ i) (hk : 0 ≤ k) (hj : 0 ≤ j) (hj' : j < 2*h) :
    liftedNewKey h i k ≤ oldKey j ↔ newKey h i k ≤ oldKey j := by
  by_cases hc : NegativeComplement h i k
  · have he := complement_key h i k hh hi hk hc
    simp only [liftedNewKey,if_pos hc,oldKey]
    omega
  · simp [liftedNewKey,hc]

#print axioms lifted_new_le_iff
#print axioms lifted_old_le_iff
#print axioms lifted_le_old_iff

def reducedKeyIndex (h s : Int) : Int :=
  if s < -h then s+2*h else if h < s then s-2*h else s

def keyOldAnchor (h z : Int) : Int :=
  if z < 0 then z+h-1 else z+h

/-- The finite auxiliary crossing is immediately before or after its old
integer anchor. The three exceptional tangent sums are excluded. -/
theorem lifted_anchor (h i k : Int) (hh : 1 ≤ h)
    (hi : 0 ≤ i) (hi' : i < 2*h) (hk : 0 ≤ k) (hk' : k < 2*h)
    (hz : i+k-2*h+1 ≠ 0) (hn : i+k-2*h+1 ≠ -h)
    (hp : i+k-2*h+1 ≠ h) :
    liftedNewKey h i k = 4*keyOldAnchor h (reducedKeyIndex h (i+k-2*h+1)) +
      (if (i < h ∧ k < h) ∨
        (((i < h ∧ h ≤ k) ∨ (k < h ∧ h ≤ i)) ∧ 0 < i+k-2*h+1)
       then 1 else 3) := by
  unfold liftedNewKey NegativeComplement newKey keyOldAnchor reducedKeyIndex
  split_ifs <;> omega

#print axioms lifted_anchor
end Kobon.BBLLiftedKeys
