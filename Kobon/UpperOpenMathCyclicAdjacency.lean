import Kobon.UpperOpenMathRadialOrder

/-! In the canonical cyclic order, a positive wedge that is not consecutive
contains the next incident ray strictly in its interior.  The arithmetic
argument accounts for both half-plane transitions and the cyclic wrap. -/
namespace Kobon.UpperOpenMathCyclicAdjacency
open UpperOpenMathRadialOrder

def cross (u v : Point) : ℝ := u.1*v.2-u.2*v.1

theorem cross_swap (u v : Point) : cross v u = -cross u v := by
  dsimp [cross]
  ring

theorem cross_neg_left (u v : Point) :
    cross (-u.1,-u.2) v = -cross u v := by
  dsimp [cross]
  ring

theorem cross_neg_right (u v : Point) :
    cross u (-v.1,-v.2) = -cross u v := by
  dsimp [cross]
  ring

def IndexPositive (r a b : ℕ) : Prop :=
  if a<r then
    if b<r then a<b else b-r<a
  else
    if b<r then b<a-r else a<b

theorem positive_successor (r a b : ℕ) (hr : 2≤r)
    (ha : a<2*r) (hb : b<2*r) (hp : IndexPositive r a b)
    (hne : b≠if a+1=2*r then 0 else a+1) :
    IndexPositive r (if a+1=2*r then 0 else a+1) b := by
  unfold IndexPositive at *
  split_ifs at * <;> omega

variable {n : ℕ} {L : ℕ → Line ℝ} {S : Finset (Fin n)}
  (D : OrderedDirections n L S)

theorem vector_cross_pos_iff (a b : Fin S.card) :
    0<cross (D.vector a) (D.vector b) ↔ a<b := by
  unfold cross
  rw [D.vector_det,sub_pos]
  exact D.increasing.lt_iff_lt

section Cyclic
variable [NeZero (2*S.card)]

theorem cyclic_cross_pos_iff (a b : ZMod (2*S.card)) :
    0<cross (D.cyclicVector a) (D.cyclicVector b) ↔
      IndexPositive S.card a.val b.val := by
  have hav := ZMod.val_lt a
  have hbv := ZMod.val_lt b
  by_cases ha : a.val<S.card <;> by_cases hb : b.val<S.card
  · unfold OrderedDirections.cyclicVector
    rw [dif_pos ha,dif_pos hb]
    simpa only [IndexPositive,ha,hb,ite_true,Fin.lt_def] using
      vector_cross_pos_iff D (⟨a.val,ha⟩ : Fin S.card) ⟨b.val,hb⟩
  · unfold OrderedDirections.cyclicVector
    rw [dif_pos ha,dif_neg hb,cross_neg_right,← cross_swap]
    simpa only [IndexPositive,ha,hb,ite_true,ite_false,Fin.lt_def] using
      vector_cross_pos_iff D (⟨b.val-S.card,by omega⟩ : Fin S.card) ⟨a.val,ha⟩
  · unfold OrderedDirections.cyclicVector
    rw [dif_neg ha,dif_pos hb,cross_neg_left,← cross_swap]
    simpa only [IndexPositive,ha,hb,ite_true,ite_false,Fin.lt_def] using
      vector_cross_pos_iff D (⟨b.val,hb⟩ : Fin S.card) ⟨a.val-S.card,by omega⟩
  · unfold OrderedDirections.cyclicVector
    rw [dif_neg ha,dif_neg hb,cross_neg_left,cross_neg_right,neg_neg]
    have hh := vector_cross_pos_iff D
      (⟨a.val-S.card,by omega⟩ : Fin S.card) ⟨b.val-S.card,by omega⟩
    simp only [Fin.lt_def] at hh
    simp only [IndexPositive,ha,hb,ite_false]
    exact hh.trans (by omega)

theorem successor_val (hr : 2≤S.card) (z : ZMod (2*S.card)) :
    (z+1).val=if z.val+1=2*S.card then 0 else z.val+1 := by
  have hv := ZMod.val_lt z
  have h1 : (1 : ZMod (2*S.card)).val=1 := by
    simpa only [Nat.cast_one] using
      (ZMod.val_natCast_of_lt (n:=2*S.card) (a:=1) (by omega))
  rw [ZMod.val_add,h1]
  split_ifs with h
  · rw [h,Nat.mod_self]
  · exact Nat.mod_eq_of_lt (by omega)

/-- A triangle with nonconsecutive radial sides has an incident direction
strictly between them; the geometric no-cut lemma can then exclude it. -/
theorem next_inside_positive_wedge (hr : 2≤S.card)
    (a b : ZMod (2*S.card))
    (hp : 0<cross (D.cyclicVector a) (D.cyclicVector b))
    (hne : b≠a+1) :
    0<cross (D.cyclicVector (a+1)) (D.cyclicVector b) := by
  have hp' := (cyclic_cross_pos_iff D a b).mp hp
  have hn : b.val≠if a.val+1=2*S.card then 0 else a.val+1 := by
    intro he
    apply hne
    apply ZMod.val_injective (2*S.card)
    rw [successor_val hr a]
    exact he
  apply (cyclic_cross_pos_iff D (a+1) b).mpr
  rw [successor_val hr a]
  exact positive_successor S.card a.val b.val hr (ZMod.val_lt a) (ZMod.val_lt b) hp' hn

end Cyclic
#print axioms next_inside_positive_wedge
end Kobon.UpperOpenMathCyclicAdjacency
