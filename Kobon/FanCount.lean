import Kobon.FanGeometry
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Counting ordinary shared rays in a cyclic fan

The geometric no-long-run obstruction from `FanGeometry` says that r-1
consecutive rays cannot all be shared segments with ordinary other endpoints.
The theorem here supplies the exact cyclic double count: at most 2r-3 of the
2r rays can be selected. The cyclic extraction from a full arrangement remains
an explicit interface, rather than an asserted geometric upper theorem.
-/
namespace Kobon.FanCount
open scoped BigOperators
open Finset

theorem window_bound (r : ℕ) [NeZero (2*r)] (S : Finset (ZMod (2*r)))
    (start : ZMod (2*r))
    (h : ∃ j : Fin (r-1), start+(j.val : ZMod (2*r))∉S) :
    (∑ j : Fin (r-1), if start+(j.val : ZMod (2*r))∈S then 1 else 0) ≤ r-2 := by
  classical
  rcases h with ⟨j,hj⟩
  have he := Finset.sum_erase_add
    (univ : Finset (Fin (r-1)))
    (fun k : Fin (r-1) => if start+(k.val : ZMod (2*r))∈S then (1:ℕ) else 0)
    (mem_univ j)
  simp only [hj,if_false,add_zero] at he
  rw [← he]
  calc
    _ ≤ ∑ _k ∈ (univ : Finset (Fin (r-1))).erase j, (1:ℕ) := by
      apply sum_le_sum
      intro k hk
      split <;> omega
    _ = r-2 := by simp [Nat.sub_sub]

theorem ordinary_shared_ray_bound (r : ℕ) (hr : 3≤r) (S : Finset (ZMod (2*r)))
    (h : ∀ start : ZMod (2*r), ∃ j : Fin (r-1),
      start+(j.val : ZMod (2*r))∉S) : S.card≤2*r-3 := by
  classical
  have hn : 2*r≠0 := by omega
  letI : NeZero (2*r) := ⟨hn⟩
  let f : ZMod (2*r) → ℕ := fun x => if x∈S then 1 else 0
  have hf : (∑ x : ZMod (2*r), f x)=S.card := by simp [f]
  have hshift (j : Fin (r-1)) :
      (∑ x : ZMod (2*r), f (x+(j.val : ZMod (2*r))))=S.card := by
    rw [← hf]
    exact Equiv.sum_comp (Equiv.addRight (j.val : ZMod (2*r))) f
  have htotal :
      (∑ x : ZMod (2*r), ∑ j : Fin (r-1), f (x+(j.val : ZMod (2*r))))
        = (r-1)*S.card := by
    rw [sum_comm]
    simp [hshift]
  have hle :
      (∑ x : ZMod (2*r), ∑ j : Fin (r-1), f (x+(j.val : ZMod (2*r))))
        ≤ 2*r*(r-2) := by
    calc
      _ ≤ ∑ _x : ZMod (2*r), (r-2) := by
        apply sum_le_sum
        intro x hx
        exact window_bound r S x (h x)
      _ = 2*r*(r-2) := by simp [ZMod.card]
  rw [htotal] at hle
  by_contra hs
  have hcard : 2*(r-1)≤S.card := by omega
  have hm := Nat.mul_le_mul_left (r-1) hcard
  have h1 : r-1+1=r := by omega
  have h2 : r-2+2=r := by omega
  nlinarith

#print axioms ordinary_shared_ray_bound

end Kobon.FanCount
