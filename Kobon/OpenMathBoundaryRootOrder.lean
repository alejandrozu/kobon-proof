import Kobon.OpenMathBoundarySampleExistence
import Mathlib.Data.Finset.Sort

/-! Finite ordering facts for actual critical normal values. Sorting supplies
one permutation, and exclusion of intermediate critical values forces adjacent
ranks. These lemmas concern real finite sequences and have no geometric premise.
-/
namespace Kobon.OpenMathBoundaryRootOrder
open scoped BigOperators
set_option autoImplicit false

theorem exists_increasing_permutation {m : Nat} (f : Fin m → ℝ)
    (hf : Function.Injective f) :
    ∃ σ : Equiv.Perm (Fin m), StrictMono (fun i => f (σ i)) := by
  classical
  let s : Finset ℝ := Finset.univ.image f
  have hs : s.card=m := by
    dsimp [s]
    rw [Finset.card_image_of_injective _ hf]
    simp
  let g : Fin m → s := fun i => ⟨f i,Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩⟩
  have hg : Function.Bijective g := by
    constructor
    · intro i j h
      apply hf
      exact congrArg Subtype.val h
    · intro y
      have hy : y.val∈Finset.univ.image f := y.property
      rcases Finset.mem_image.mp hy with ⟨i,_,hi⟩
      exact ⟨i,Subtype.ext hi⟩
  let e : Fin m ≃ s := Equiv.ofBijective g hg
  let o : Fin m ≃o s := s.orderIsoOfFin hs
  let σ : Equiv.Perm (Fin m) := o.toEquiv.trans e.symm
  have he : ∀ i, f (σ i)=(o i).val := by
    intro i
    exact congrArg Subtype.val (e.apply_symm_apply (o i))
  refine ⟨σ,?_⟩
  intro i j hij
  change f (σ i)<f (σ j)
  rw [he i,he j]
  exact o.strictMono hij

theorem adjacent_of_no_between {m : Nat} (roots : Fin m → ℝ)
    (hr : StrictMono roots) (i j : Fin m) (hij : roots i<roots j)
    (hgap : ∀ k, ¬(roots i<roots k ∧ roots k<roots j)) :
    i.val+1=j.val := by
  have hi : i<j := hr.lt_iff_lt.mp hij
  have hiv : i.val<j.val := hi
  by_contra he
  have hk : i.val+1<j.val := by omega
  let k : Fin m := ⟨i.val+1,by have := j.isLt; omega⟩
  apply hgap k
  constructor
  · exact hr (by change i.val<k.val; dsimp [k]; omega)
  · exact hr (by change k.val<j.val; exact hk)

theorem first_of_no_smaller {m : Nat} (roots : Fin m → ℝ)
    (hr : StrictMono roots) (j : Fin m)
    (h : ∀ k, ¬roots k<roots j) : j.val=0 := by
  by_contra hj
  let k : Fin m := ⟨0,by have := j.isLt; omega⟩
  exact h k (hr (by change k.val<j.val; dsimp [k]; omega))

theorem last_of_no_larger {m : Nat} (roots : Fin m → ℝ)
    (hr : StrictMono roots) (i : Fin m)
    (h : ∀ k, ¬roots i<roots k) : i.val+1=m := by
  by_contra hi
  let k : Fin m := ⟨i.val+1,by have := i.isLt; omega⟩
  exact h k (hr (by change i.val<k.val; dsimp [k]; omega))

/-- The exact integer gain supplied by boundary-sector averaging at odd order
`2*m+1`. There are two normal representatives for each of the `2*m+1` sectors.
The deficit-two lower sum is already enough to force an `m`-triangle choice. -/
theorem exists_half_gain {α : Type*} [Fintype α] (m : Nat) (hm : 1 ≤ m)
    (hc : Fintype.card α=4*m+2) (f : α → Nat)
    (hs : 2*m*(2*m-1) ≤ ∑ i, f i) : ∃ i, m ≤ f i := by
  classical
  by_contra h
  push Not at h
  have hb : ∀ i, f i ≤ m-1 := by intro i; have := h i; omega
  have hu : (∑ i, f i) ≤ (4*m+2)*(m-1) := by
    calc
      _ ≤ ∑ _i : α, (m-1) := Finset.sum_le_sum (fun i _ => hb i)
      _ = _ := by simp [hc]
  have hsub : m-1+1=m := by omega
  have hsub' : 2*m-1+1=2*m := by omega
  nlinarith

#print axioms exists_increasing_permutation
#print axioms adjacent_of_no_between
#print axioms exists_half_gain
end Kobon.OpenMathBoundaryRootOrder
