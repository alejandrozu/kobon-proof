import Kobon.FurediPalastiCount

/-! A repeated-index correction for a phase variant of the classical
Furedi--Palasti construction. The zero triple belongs to all three bad sets,
so the earlier union bound can be sharpened by two ordered triples. -/
namespace Kobon.ShiftedCount
open Finset FurediPalastiCount

variable (n : ℕ) [NeZero n]

theorem card_bad_zero : (bad n 0).card + 2 ≤ 3*n := by
  classical
  let A : Finset (FurediPalastiCount.Triple n) :=
    univ.image (fun i : ZMod n => (i,i,0-i-i))
  let B : Finset (FurediPalastiCount.Triple n) :=
    univ.image (fun i : ZMod n => (i,0-i-i,i))
  let C : Finset (FurediPalastiCount.Triple n) :=
    univ.image (fun i : ZMod n => (0-i-i,i,i))
  have ha : A.card ≤ n := by simpa [A,ZMod.card] using
    (card_image_le (s:=univ) (f:=fun i : ZMod n => (i,i,0-i-i)))
  have hb : B.card ≤ n := by simpa [B,ZMod.card] using
    (card_image_le (s:=univ) (f:=fun i : ZMod n => (i,0-i-i,i)))
  have hc : C.card ≤ n := by simpa [C,ZMod.card] using
    (card_image_le (s:=univ) (f:=fun i : ZMod n => (0-i-i,i,i)))
  have hzA : (0,0,0) ∈ A := by simp [A]
  have hzB : (0,0,0) ∈ B := by simp [B]
  have hzC : (0,0,0) ∈ C := by simp [C]
  have hAB : 1 ≤ (A ∩ B).card := card_pos.mpr ⟨(0,0,0),mem_inter.mpr ⟨hzA,hzB⟩⟩
  have hABC : 1 ≤ ((A ∪ B) ∩ C).card := card_pos.mpr
    ⟨(0,0,0),mem_inter.mpr ⟨mem_union_left B hzA,hzC⟩⟩
  have h1 := card_union_add_card_inter A B
  have h2 := card_union_add_card_inter (A ∪ B) C
  change ((A ∪ B) ∪ C).card + 2 ≤ 3*n
  omega

theorem good_count_plus (b : ZMod n) (hb : (0:ZMod n)≠b) :
    2*(n*n)+2 ≤ (good n 0 b).card+6*n := by
  classical
  let all := fiber n 0 ∪ fiber n b
  have hc : all.card=2*(n*n) := by
    dsimp [all]
    rw [card_union_of_disjoint (disjoint_fiber n 0 b hb),card_fiber,card_fiber]
    omega
  have hsplit := card_filter_add_card_filter_not (s:=all) (p:=distinct n)
  have hsub : all.filter (fun p => ¬distinct n p) ⊆ bad n 0 ∪ bad n b := by
    intro p hp
    rcases mem_filter.mp hp with ⟨hp,hd⟩
    rcases mem_union.mp hp with hp | hp
    · exact mem_union_left _ (mem_bad n 0 p ((mem_fiber n 0 p).mp hp) hd)
    · exact mem_union_right _ (mem_bad n b p ((mem_fiber n b p).mp hp) hd)
  have hle := card_le_card hsub
  have hu := card_union_le (bad n 0) (bad n b)
  have hba := card_bad_zero n
  have hbb := card_bad_le n b
  change (good n 0 b).card+_=_ at hsplit
  rw [hc] at hsplit
  omega

theorem ordered_bound_plus (hn : 3≤n) (b : ZMod n) (hb : (0:ZMod n)≠b) :
    n*(n-3)/3+1 ≤ (ordered n 0 b).card := by
  have h1 := good_count_plus n b hb
  have h2 := good_le_six_ordered n 0 b
  have h3 : n-3+3=n := by omega
  have h4 : n*(n-3)+1 ≤ 3*(ordered n 0 b).card := by nlinarith
  omega

#print axioms ordered_bound_plus
end Kobon.ShiftedCount
