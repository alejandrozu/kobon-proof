import Kobon.BBLVisible
import Kobon.BBLVisibleRetention

/-! Finite assembly of the visible wedges after a BBL doubling. -/
namespace Kobon.BBLVisibleAssembly
open Exterior BBLRowGeometry BBLVisible BBLVisibleRetention

def shift (r : Nat) (t : Triple) : Triple := ⟨t.i-1,t.j-1,8*r+1⟩

theorem shift_injective (r : Nat) (t u : Triple)
    (hti : 0 < t.i) (htij : t.i < t.j) (htk : t.k=4*r+1)
    (hui : 0 < u.i) (huij : u.i < u.j) (huk : u.k=4*r+1)
    (he : shift r t=shift r u) : t=u := by
  have h1 := congrArg Triple.i he
  have h2 := congrArg Triple.j he
  dsimp [shift] at h1 h2
  cases t
  cases u
  simp only [Triple.mk.injEq]
  dsimp at *
  omega

theorem visible_gain (r V : Nat) (hr : 1 ≤ r) (old new : Nat → Line ℝ)
    (w : Line ℝ) (vs : List Triple) (hn : vs.Nodup)
    (hpold : NoParallel (4*r+1) old) (hsold : NoConcurrent (4*r+1) old)
    (hwold : Admissible (4*r+1) old w)
    (hvo : ∀ t ∈ vs, VisiblePair (4*r+1) old w t) (hcount : V ≤ vs.length)
    (hp : NoParallel (8*r+1) new) (hs : NoConcurrent (8*r+1) new)
    (hw : Admissible (8*r+1) new w) (horder : CrossingOrder r new w)
    (hretained : ∀ t ∈ vs, t.i ≠ 0 → VisiblePair (8*r+1) new w (shift r t))
    (hcentral : VisiblePair (8*r+1) new w ⟨4*r-1,7*r-1,8*r+1⟩) :
    ∃ ws : List Triple, ws.Nodup ∧ (∀ t ∈ ws, VisiblePair (8*r+1) new w t) ∧
      V+2*r ≤ ws.length := by
  let retained := vs.filter (fun t => decide (t.i ≠ 0))
  have hmem (t : Triple) : t ∈ retained ↔ t ∈ vs ∧ t.i ≠ 0 := by
    simp [retained]
  have hfiltered : retained.Nodup := hn.filter _
  let shifted := retained.map (shift r)
  have hshifted : shifted.Nodup := by
    apply List.Nodup.map_on ?_ hfiltered
    intro t ht u hu he
    obtain ⟨ht,hti⟩ := (hmem t).mp ht
    obtain ⟨hu,hui⟩ := (hmem u).mp hu
    have htold := hvo t ht
    have huold := hvo u hu
    exact shift_injective r t u (by omega) htold.1 htold.2.2.1
      (by omega) huold.1 huold.2.2.1 he
  have hshiftFacts : ∀ t ∈ shifted, VisiblePair (8*r+1) new w t ∧ t.j < 4*r := by
    intro t ht
    obtain ⟨u,hu,rfl⟩ := List.mem_map.mp ht
    obtain ⟨hu,hui⟩ := (hmem u).mp hu
    have huold := hvo u hu
    exact ⟨hretained u hu hui,by have h1 := huold.1; have h2 := huold.2.1; dsimp [shift]; omega⟩
  obtain ⟨fresh,hfn,hfv,hfc⟩ := new_visible_witness r hr new w hp hs hw horder hcentral
  have hdisjoint : shifted.Disjoint fresh := by
    intro t ht hf
    have hlt := (hshiftFacts t ht).2
    have hge := (hfv t hf).2
    omega
  refine ⟨shifted++fresh,hshifted.append hfn hdisjoint,?_,?_⟩
  · intro t ht
    rcases List.mem_append.mp ht with ht | ht
    · exact (hshiftFacts t ht).1
    · exact (hfv t ht).1
  · have hret := retain_all_but_one (4*r+1) old w hpold hsold hwold vs hn hvo
    change vs.length ≤ retained.length+1 at hret
    dsimp [shifted]
    rw [List.length_append,List.length_map,hfc]
    omega

#print axioms visible_gain
end Kobon.BBLVisibleAssembly
