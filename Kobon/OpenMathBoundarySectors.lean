import Kobon.OpenMathBoundaryNormals
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! Finite normal-sector counting. Opposite normal representatives contribute
one joint positive choice when the two scalar projections have the same sign.
Adjacent critical values exclude exactly one of the n projective sectors.
No triangle count is assumed in this combinatorial lemma.
-/
namespace Kobon.OpenMathBoundarySectors
open Finset
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1000000

def signedValue (b : Bool) (x : ℝ) : ℝ := if b then -x else x

noncomputable def choices (f g : ℝ) : Finset Bool := by
  classical
  exact univ.filter (fun b => 0<signedValue b f ∧ 0<signedValue b g)

noncomputable def choiceCount (f g : ℝ) : Nat := (choices f g).card

theorem choiceCount_formula (f g : ℝ) :
    choiceCount f g=(if 0<f ∧ 0<g then 1 else 0)+(if f<0 ∧ g<0 then 1 else 0) := by
  classical
  have he : choices f g=(if 0<f ∧ 0<g then {false} else ∅) ∪
      (if f<0 ∧ g<0 then {true} else ∅) := by
    by_cases hp : 0<f ∧ 0<g <;> by_cases hn : f<0 ∧ g<0
    all_goals
      ext x
      cases x <;> simp [choices,signedValue,hp,hn]
  unfold choiceCount
  rw [he]
  by_cases hp : 0<f ∧ 0<g <;> by_cases hn : f<0 ∧ g<0 <;> simp [hp,hn]

theorem choiceCount_product (f g : ℝ) : choiceCount f g=if 0<f*g then 1 else 0 := by
  rw [choiceCount_formula]
  by_cases hp : 0<f ∧ 0<g
  · have hn : ¬(f<0 ∧ g<0) := by rintro ⟨hf,_⟩; linarith [hp.1]
    simp [mul_pos_iff,hp,hn]
  · by_cases hn : f<0 ∧ g<0 <;> simp [mul_pos_iff,hp,hn]
/-- Abstract exact projective samples: n-1 distinct sorted critical roots
and one sample in each of the n complementary intervals. -/
structure Samples (n : Nat) where
  roots : Fin (n-1)→ℝ
  sample : Fin n→ℝ
  left : ∀ (k : Fin n) (i : Fin (n-1)), roots i<sample k ↔ i.val<k.val
  right : ∀ (k : Fin n) (i : Fin (n-1)), sample k<roots i ↔ k.val ≤ i.val

/-- A missing sample leaves exactly n-1 unit contributions. -/
theorem sum_except_one (n : Nat) (bad : Fin n) :
    (∑ k : Fin n, if k=bad then 0 else 1)=n-1 := by
  have hp : ∀ k : Fin n, (if k=bad then 0 else 1)+(if k=bad then 1 else 0)=(1 : Nat) := by
    intro k
    split_ifs <;> simp
  have hh : (∑ k : Fin n, ((if k=bad then 0 else 1)+(if k=bad then 1 else 0)))=
      ∑ _k : Fin n, (1 : Nat) := Finset.sum_congr rfl (fun k _ => hp k)
  simp only [Finset.sum_add_distrib] at hh
  have he : (∑ k : Fin n, if k=bad then (1 : Nat) else 0)=1 := by simp
  have hn : (∑ _k : Fin n, (1 : Nat))=n := by simp
  rw [he,hn] at hh
  omega

theorem adjacent_sample_product (n : Nat) (D : Samples n)
    (i j : Fin (n-1)) (hij : i.val+1=j.val) (a b : ℝ) (hab : 0<a*b)
    (k : Fin n) :
    0<(a*(D.sample k-D.roots i))*(b*(D.sample k-D.roots j)) ↔ k.val≠j.val := by
  have he : (a*(D.sample k-D.roots i))*(b*(D.sample k-D.roots j))=
      (a*b)*((D.sample k-D.roots i)*(D.sample k-D.roots j)) := by ring
  rw [he]
  constructor
  · intro hp hk
    have hl := (D.left k i).mpr (by omega)
    have hr := (D.right k j).mpr (by omega)
    have hd := mul_neg_of_pos_of_neg (sub_pos.mpr hl) (sub_neg.mpr hr)
    have hn := mul_neg_of_pos_of_neg hab hd
    linarith
  · intro hk
    have hcase : k.val ≤ i.val ∨ j.val<k.val := by omega
    rcases hcase with hleft|hright
    · have hi := (D.right k i).mpr hleft
      have hj := (D.right k j).mpr (by omega)
      exact mul_pos hab (mul_pos_of_neg_of_neg (sub_neg.mpr hi) (sub_neg.mpr hj))
    · have hi := (D.left k i).mpr (by omega)
      have hj := (D.left k j).mpr hright
      exact mul_pos hab (mul_pos (sub_pos.mpr hi) (sub_pos.mpr hj))

/-- The n projective representatives and their n opposites select the
adjacent pair jointly in exactly n-1 cases. -/
theorem adjacent_sector_count (n : Nat) (D : Samples n)
    (i j : Fin (n-1)) (hij : i.val+1=j.val) (a b : ℝ) (hab : 0<a*b) :
    (∑ k : Fin n, choiceCount (a*(D.sample k-D.roots i))
      (b*(D.sample k-D.roots j)))=n-1 := by
  let bad : Fin n := ⟨j.val,by have := j.isLt; omega⟩
  have he : ∀ k : Fin n, choiceCount (a*(D.sample k-D.roots i))
      (b*(D.sample k-D.roots j))=if k=bad then 0 else 1 := by
    intro k
    rw [choiceCount_product]
    by_cases hp : 0<(a*(D.sample k-D.roots i))*(b*(D.sample k-D.roots j))
    · have hn := (adjacent_sample_product n D i j hij a b hab k).mp hp
      have hk : k≠bad := by intro he; exact hn (congrArg Fin.val he)
      rw [if_pos hp,if_neg hk]
    · have hk : k=bad := by
        apply Fin.ext
        by_contra hn
        exact hp ((adjacent_sample_product n D i j hij a b hab k).mpr hn)
      rw [if_neg hp,if_pos hk]
  simp_rw [he]
  exact sum_except_one n bad

theorem first_root_count (n : Nat) (D : Samples n) (h : 1<n)
    (a b : ℝ) (hab : 0<a*b) :
    (∑ k : Fin n, choiceCount a (b*(D.sample k-D.roots ⟨0,by omega⟩)))=n-1 := by
  let bad : Fin n := ⟨0,by omega⟩
  have he : ∀ k : Fin n, choiceCount a (b*(D.sample k-D.roots ⟨0,by omega⟩))=
      if k=bad then 0 else 1 := by
    intro k
    rw [choiceCount_product]
    have hmul : a*(b*(D.sample k-D.roots ⟨0,by omega⟩))=
        (a*b)*(D.sample k-D.roots ⟨0,by omega⟩) := by ring
    rw [hmul]
    by_cases hk : k=bad
    · have hk0 : k.val=0 := by simp [hk,bad]
      have hlt := (D.right k ⟨0,by omega⟩).mpr (by omega)
      have hn := mul_neg_of_pos_of_neg hab (sub_neg.mpr hlt)
      simp only [if_neg (not_lt_of_ge hn.le),if_pos hk]
    · have hkv : 0<k.val := by have hh : k.val≠0 := fun hh => hk (Fin.ext hh); omega
      have hlt := (D.left k ⟨0,by omega⟩).mpr hkv
      have hp := mul_pos hab (sub_pos.mpr hlt)
      simp [hk,hp]
  simp_rw [he]
  exact sum_except_one n bad

theorem last_root_count (n : Nat) (D : Samples n) (h : 1<n)
    (a b : ℝ) (hab : a*b<0) :
    (∑ k : Fin n, choiceCount a (b*(D.sample k-D.roots ⟨n-2,by omega⟩)))=n-1 := by
  let bad : Fin n := ⟨n-1,by omega⟩
  have he : ∀ k : Fin n, choiceCount a (b*(D.sample k-D.roots ⟨n-2,by omega⟩))=
      if k=bad then 0 else 1 := by
    intro k
    rw [choiceCount_product]
    have hmul : a*(b*(D.sample k-D.roots ⟨n-2,by omega⟩))=
        (a*b)*(D.sample k-D.roots ⟨n-2,by omega⟩) := by ring
    rw [hmul]
    by_cases hk : k=bad
    · have hkv : k.val=n-1 := by simp [hk,bad]
      have hlt := (D.left k ⟨n-2,by omega⟩).mpr (by omega)
      have hn := mul_neg_of_neg_of_pos hab (sub_pos.mpr hlt)
      simp only [if_neg (not_lt_of_ge hn.le),if_pos hk]
    · have hkv : k.val ≤ n-2 := by
        have hh : k.val≠n-1 := fun hh => hk (Fin.ext hh)
        have := k.isLt
        omega
      have hlt := (D.right k ⟨n-2,by omega⟩).mpr hkv
      have hp := mul_pos_of_neg_of_neg hab (sub_neg.mpr hlt)
      simp only [if_pos hp,if_neg hk]
  simp_rw [he]
  exact sum_except_one n bad
#print axioms choiceCount_product
#print axioms adjacent_sector_count
#print axioms first_root_count
end Kobon.OpenMathBoundarySectors