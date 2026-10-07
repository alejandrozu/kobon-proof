import Kobon.OpenMathBoundarySectors
import Mathlib.Order.Fin.Basic

/-! Explicit samples of every complementary interval of an increasing finite
real root sequence. The construction has no generic-position or computability
premise: end intervals use offsets by one and internal intervals use midpoints.
-/
namespace Kobon.OpenMathBoundarySampleExistence
set_option autoImplicit false

noncomputable def sample {n : Nat} (hn : 2 ≤ n)
    (roots : Fin (n-1) → ℝ) (k : Fin n) : ℝ :=
  if hk : k.val=0 then roots ⟨0,by omega⟩-1
  else if hl : k.val=n-1 then roots ⟨n-2,by omega⟩+1
  else (roots ⟨k.val-1,by omega⟩+roots ⟨k.val,by omega⟩)/2

theorem sample_separates {n : Nat} (hn : 2 ≤ n)
    (roots : Fin (n-1) → ℝ) (hr : StrictMono roots)
    (k : Fin n) (i : Fin (n-1)) :
    (i.val<k.val → roots i<sample hn roots k) ∧
    (k.val ≤ i.val → sample hn roots k<roots i) := by
  have hklt := k.isLt
  have hilt := i.isLt
  by_cases hz : k.val=0
  · rw [sample,dif_pos hz]
    constructor
    · omega
    · intro _
      have he : roots ⟨0,by omega⟩ ≤ roots i :=
        hr.monotone (by change 0 ≤ i.val; omega)
      linarith
  · by_cases hl : k.val=n-1
    · rw [sample,dif_neg hz,dif_pos hl]
      constructor
      · intro _
        have he : roots i ≤ roots ⟨n-2,by omega⟩ :=
          hr.monotone (by change i.val ≤ n-2; omega)
        linarith
      · omega
    · rw [sample,dif_neg hz,dif_neg hl]
      have hgap : roots ⟨k.val-1,by omega⟩<roots ⟨k.val,by omega⟩ :=
        hr (by change k.val-1<k.val; omega)
      constructor
      · intro hi
        have he : roots i ≤ roots ⟨k.val-1,by omega⟩ :=
          hr.monotone (by change i.val ≤ k.val-1; omega)
        linarith
      · intro hi
        have he : roots ⟨k.val,by omega⟩ ≤ roots i :=
          hr.monotone (by change k.val ≤ i.val; omega)
        linarith

theorem root_lt_sample_iff {n : Nat} (hn : 2 ≤ n)
    (roots : Fin (n-1) → ℝ) (hr : StrictMono roots)
    (k : Fin n) (i : Fin (n-1)) :
    roots i<sample hn roots k ↔ i.val<k.val := by
  have h := sample_separates hn roots hr k i
  constructor
  · intro hi
    by_contra he
    have hnle : k.val ≤ i.val := Nat.le_of_not_gt he
    exact (not_lt_of_gt (h.2 hnle)) hi
  · exact h.1

theorem sample_lt_root_iff {n : Nat} (hn : 2 ≤ n)
    (roots : Fin (n-1) → ℝ) (hr : StrictMono roots)
    (k : Fin n) (i : Fin (n-1)) :
    sample hn roots k<roots i ↔ k.val ≤ i.val := by
  have h := sample_separates hn roots hr k i
  constructor
  · intro hi
    by_contra he
    have hnlt : i.val<k.val := Nat.lt_of_not_ge he
    exact (not_lt_of_gt (h.1 hnlt)) hi
  · exact h.2

theorem exists_samples {n : Nat} (hn : 2 ≤ n)
    (roots : Fin (n-1) → ℝ) (hr : StrictMono roots) :
    ∃ s : Fin n → ℝ,
      (∀ k i, roots i<s k ↔ i.val<k.val) ∧
      (∀ k i, s k<roots i ↔ k.val ≤ i.val) :=
  ⟨sample hn roots,root_lt_sample_iff hn roots hr,sample_lt_root_iff hn roots hr⟩

noncomputable def sectorSamples {n : Nat} (hn : 2 ≤ n)
    (roots : Fin (n-1) → ℝ) (hr : StrictMono roots) :
    Kobon.OpenMathBoundarySectors.Samples n where
  roots := roots
  sample := sample hn roots
  left := root_lt_sample_iff hn roots hr
  right := sample_lt_root_iff hn roots hr

#print axioms exists_samples
#print axioms sectorSamples
end Kobon.OpenMathBoundarySampleExistence
