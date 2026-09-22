import Kobon.BBLRowMax

/-! The new visible wedges in a BBL doubling: two auxiliary families,
the last horizontal wedge, and the central old/new wedge. -/
namespace Kobon.BBLVisible
open Exterior BBLExtrema BBLRowOrder BBLRowGeometry BBLRowMax
set_option maxHeartbeats 10000000
set_option maxRecDepth 10000

def auxPair (r p : Nat) : Nat × Nat :=
  if p < r then (p,2*r-1-p)
  else if p < 2*r-1 then (r+p,5*r-2-p)
  else (4*r-1,4*r)

theorem auxPair_bounds (r p : Nat) (hr : 1 ≤ r) (hp : p < 2*r) :
    (auxPair r p).1 < (auxPair r p).2 ∧ (auxPair r p).2 ≤ 4*r := by
  unfold auxPair
  split_ifs <;> dsimp <;> omega

theorem auxPair_keys (r p : Nat) (hr : 1 ≤ r) (hp : p < 2*r) :
    16*(r:Int)-1 ≤ newKey (2*r) (auxPair r p).1 (auxPair r p).2 ∧
    ((auxPair r p).1 < 4*r-1 ∨
      newKey (2*r) (auxPair r p).1 (auxPair r p).2=16*r) ∧
    ((auxPair r p).2 < 4*r-1 ∨
      newKey (2*r) (auxPair r p).1 (auxPair r p).2=16*r) := by
  unfold auxPair
  split_ifs <;> dsimp <;> unfold newKey <;> push_cast <;> split_ifs <;> omega

theorem key_row_max (r i k : Nat) (hr : 1 ≤ r)
    (hi : i ≤ 4*r) (hk : k ≤ 4*r) (hik : i ≠ k)
    (hkey : 16*(r:Int)-1 ≤ newKey (2*r) i k)
    (hrow : i < 4*r-1 ∨ newKey (2*r) i k=16*r) :
    ∀ s : Fin (8*r+1), s.val ≠ 4*r+i → crossKey r i s ≤ newKey (2*r) i k := by
  intro s hsi
  unfold crossKey
  split_ifs with hs
  · unfold oldKey
    omega
  · have hl : 0 ≤ (s.val:Int)-4*(r:Int) := by omega
    have hlu : (s.val:Int)-4*(r:Int) ≤ 2*(2*(r:Int)) := by omega
    have hne : (i:Int) ≠ (s.val:Int)-4*(r:Int) := by omega
    rcases hrow with hrow | hrow
    · have hb := row_bound_not_last (2*r) i ((s.val:Int)-4*r)
        (by omega) (by omega) (by omega) hl hlu hne
      omega
    · have hb := (key_bounds (2*r) i ((s.val:Int)-4*r)
        (by omega) (by omega) (by omega) hl hlu hne).2
      omega

def auxVisible (r p : Nat) : Triple :=
  ⟨4*r+(auxPair r p).1,4*r+(auxPair r p).2,8*r+1⟩

theorem auxVisible_injective (r p q : Nat) (hr : 1 ≤ r)
    (hp : p < 2*r) (hq : q < 2*r) (he : auxVisible r p=auxVisible r q) : p=q := by
  have h := congrArg Triple.i he
  unfold auxVisible auxPair at h
  split_ifs at h <;> dsimp at h <;> omega

theorem aux_visible (r p : Nat) (hr : 1 ≤ r) (hpp : p < 2*r)
    (L : Nat → Line ℝ) (w : Line ℝ)
    (hp : NoParallel (8*r+1) L) (hs : NoConcurrent (8*r+1) L)
    (hw : Admissible (8*r+1) L w) (horder : CrossingOrder r L w) :
    VisiblePair (8*r+1) L w (auxVisible r p) := by
  obtain ⟨hik,hk⟩ := auxPair_bounds r p hr hpp
  have hi : (auxPair r p).1 ≤ 4*r := by omega
  obtain ⟨hkey,hirow,hkrow⟩ := auxPair_keys r p hr hpp
  have hsymm : newKey (2*r) (auxPair r p).2 (auxPair r p).1=
      newKey (2*r) (auxPair r p).1 (auxPair r p).2 := by
    apply newKey_symm <;> omega
  apply max_pair_visible r _ _ L w hp hs hw horder hi hk hik
  · exact key_row_max r _ _ hr hi hk (by omega) hkey hirow
  · apply key_row_max r _ _ hr hk hi (by omega)
    · simpa only [hsymm] using hkey
    · simpa only [hsymm] using hkrow

theorem auxiliary_witness (r : Nat) (hr : 1 ≤ r) (L : Nat → Line ℝ) (w : Line ℝ)
    (hp : NoParallel (8*r+1) L) (hs : NoConcurrent (8*r+1) L)
    (hw : Admissible (8*r+1) L w) (horder : CrossingOrder r L w) :
    ∃ vs : List Triple, vs.Nodup ∧
      (∀ t ∈ vs, VisiblePair (8*r+1) L w t ∧ 4*r ≤ t.i) ∧ vs.length=2*r := by
  refine ⟨(List.range (2*r)).map (auxVisible r),List.Nodup.map_on ?_ List.nodup_range,?_,by simp⟩
  · intro p hp' q hq' he
    exact auxVisible_injective r p q hr (List.mem_range.mp hp') (List.mem_range.mp hq') he
  · intro t ht
    obtain ⟨p,hp',rfl⟩ := List.mem_map.mp ht
    exact ⟨aux_visible r p hr (List.mem_range.mp hp') L w hp hs hw horder,
      by dsimp [auxVisible]; omega⟩

theorem central_new_key_bound (r l : Nat) (hr : 1 ≤ r) (hl : l ≤ 4*r)
    (hne : l ≠ 3*r-1) : newKey (2*r) (3*r-1) l ≤ 16*r-2 := by
  unfold newKey
  push_cast
  split_ifs <;> omega

/-- The crossing order supplies the new-line half of the old R/new central
pair. Only the actual maximum along the rightmost old line is an input. -/
theorem central_visible (r : Nat) (hr : 1 ≤ r) (L : Nat → Line ℝ) (w : Line ℝ)
    (hp : NoParallel (8*r+1) L) (hs : NoConcurrent (8*r+1) L)
    (hw : Admissible (8*r+1) L w) (horder : CrossingOrder r L w)
    (hR : ∀ s : Fin (8*r+1), s.val ≠ 4*r-1 → s.val ≠ 7*r-1 →
      projection w (intersection (L (4*r-1)) (L s)) <
        projection w (intersection (L (4*r-1)) (L (7*r-1)))) :
    VisiblePair (8*r+1) L w ⟨4*r-1,7*r-1,8*r+1⟩ := by
  let v : Fin (8*r+1) := ⟨4*r-1,by omega⟩
  have hi : 3*r-1 ≤ 4*r := by omega
  have hv : v.val ≠ 4*r+(3*r-1) := by dsimp [v]; omega
  have hmax : ∀ s : Fin (8*r+1), s.val ≠ 4*r+(3*r-1) →
      crossKey r (3*r-1) s ≤ crossKey r (3*r-1) v := by
    intro s hsi
    have htarget : crossKey r (3*r-1) v=16*r-2 := by
      simp only [crossKey,v]
      rw [if_pos (by omega)]
      unfold oldKey
      omega
    rw [htarget]
    unfold crossKey
    split_ifs with hsmall
    · unfold oldKey
      omega
    · have hl : s.val-4*r ≤ 4*r := by omega
      have hne : s.val-4*r ≠ 3*r-1 := by omega
      have hb := central_new_key_bound r (s.val-4*r) hr hl hne
      have hcast : ((s.val-4*r:Nat):Int)=(s.val:Int)-4*(r:Int) := by omega
      rw [hcast] at hb
      have hiCast : ((3*r-1:Nat):Int)=3*(r:Int)-1 := by omega
      simpa only [hiCast] using hb
  apply extremal_visible _ L w hp hw _ (by dsimp; omega) (by dsimp; omega) rfl
  intro s hsR hsc
  change s.val ≠ 4*r-1 at hsR
  change s.val ≠ 7*r-1 at hsc
  refine ⟨hR s hsR hsc,?_⟩
  have hsc' : s.val ≠ 4*r+(3*r-1) := by omega
  have hRs : s ≠ v := by intro h; have := congrArg Fin.val h; dsimp [v] at this; omega
  have hh := row_extremal_label r (3*r-1) L w hp hs hw horder hi v hv hmax s hsc' hRs
  have hid : 4*r+(3*r-1)=7*r-1 := by omega
  rw [hid] at hh
  simpa only [v,intersection_swap (L (7*r-1)) (L (4*r-1))] using hh

theorem new_visible_witness (r : Nat) (hr : 1 ≤ r) (L : Nat → Line ℝ) (w : Line ℝ)
    (hp : NoParallel (8*r+1) L) (hs : NoConcurrent (8*r+1) L)
    (hw : Admissible (8*r+1) L w) (horder : CrossingOrder r L w)
    (hcentral : VisiblePair (8*r+1) L w ⟨4*r-1,7*r-1,8*r+1⟩) :
    ∃ vs : List Triple, vs.Nodup ∧
      (∀ t ∈ vs, VisiblePair (8*r+1) L w t ∧ 4*r ≤ t.j) ∧ vs.length=2*r+1 := by
  obtain ⟨vs,hn,hv,hc⟩ := auxiliary_witness r hr L w hp hs hw horder
  let central : Triple := ⟨4*r-1,7*r-1,8*r+1⟩
  have hnot : central ∉ vs := by
    intro hm
    have hh := (hv central hm).2
    dsimp [central] at hh
    omega
  refine ⟨central::vs,List.nodup_cons.mpr ⟨hnot,hn⟩,?_,by simp [hc]⟩
  intro t ht
  rcases List.mem_cons.mp ht with ht | ht
  · subst t
    exact ⟨hcentral,by dsimp [central]; omega⟩
  · have h := hv t ht
    exact ⟨h.1,by have hh := h.1.1; omega⟩

#print axioms aux_visible
#print axioms new_visible_witness
end Kobon.BBLVisible
