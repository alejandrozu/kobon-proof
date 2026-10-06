import Kobon.UpperCleanHalfplane

/-! A common-side lemma with multiple intersections on the cutting line.
Unlike the clean-line theorem, this permits arbitrary finite multiplicities.
The exceptional transverse lines all pass through a single pencil point.
The lemma is geometric groundwork, not yet a global parity charge. -/
namespace Kobon.UpperOpenMathCutHalfplane
open Cells FanGeometry UpperVertexBudget UpperTriangleIncidence
  UpperCoreExtraction UpperCleanHalfplane Finset
set_option autoImplicit false
set_option maxHeartbeats 1000000

def Witness (n : Nat) (L : Nat→Line ℝ) (cut : Fin n) (s : ℝ) (i : Fin n) : Prop :=
  ∃ j : Fin n, j≠cut ∧ j≠i ∧ 0<s*affineEval (L cut) (intersection (L i) (L j))

def NotConcurrent (n : Nat) (L : Nat→Line ℝ) : Prop :=
  ¬∃ p : Point, ∀ i : Fin n, affineEval (L i) p=0

/-- If all transverse intersections of one line were on the cut, the
whole arrangement would be concurrent. -/
theorem off_pencil_intersection
    (n : Nat) (L : Nat→Line ℝ) (hL : NoParallel n L)
    (notConcurrent : NotConcurrent n L) (cut i : Fin n) (hi : i≠cut) :
    ∃ j : Fin n, j≠cut ∧ j≠i ∧
      affineEval (L cut) (intersection (L i) (L j))≠0 := by
  classical
  by_contra h
  push Not at h
  let p := intersection (L cut) (L i)
  have hdi := noParallel_any n L hL cut i cut.isLt i.isLt (fun e => hi (Fin.ext e).symm)
  have hpc : affineEval (L cut) p=0 := intersection_on_left _ _ hdi
  have hpi : affineEval (L i) p=0 := intersection_on_right _ _ hdi
  apply notConcurrent
  refine ⟨p,fun k => ?_⟩
  by_cases hk : k=cut
  · simpa only [hk] using hpc
  by_cases hki : k=i
  · simpa only [hki] using hpi
  have hid := noParallel_any n L hL i k i.isLt k.isLt (fun e => hki (Fin.ext e).symm)
  have he : intersection (L i) (L k)=p := by
    exact ((intersection_eq_iff n L hL cut i hi.symm _).mpr
      ⟨h k hk hki,intersection_on_left _ _ hid⟩).symm
  rw [← he]
  exact intersection_on_right _ _ hid

/-- A single common side supplies a bounded intersection on every
transverse line, except possibly lines of one pencil. At the witness line
itself the bounded intersection is guaranteed by nonconcurrence. -/
theorem common_side_except_pencil
    (n : Nat) (L : Nat→Line ℝ) (hL : NoParallel n L)
    (notConcurrent : NotConcurrent n L) (cut : Fin n) :
    (∀ i : Fin n, i≠cut → Witness n L cut 1 i) ∨
    ∃ i : Fin n, i≠cut ∧ Witness n L cut (-1) i ∧
      (∀ k : Fin n, k≠cut → k=i ∨
        affineEval (L cut) (intersection (L i) (L k))≠0 →
        Witness n L cut (-1) k) := by
  classical
  by_cases hpos : ∀ i : Fin n, i≠cut → Witness n L cut 1 i
  · exact Or.inl hpos
  right
  push Not at hpos
  obtain ⟨i,hi,hbad⟩ := hpos
  have hle (j : Fin n) (hj : j≠cut) (hji : j≠i) :
      affineEval (L cut) (intersection (L i) (L j))≤0 := by
    by_contra hgt
    apply hbad
    exact ⟨j,hj,hji,by simp only [one_mul]; linarith⟩
  obtain ⟨j,hj,hji,hjoff⟩ := off_pencil_intersection n L hL notConcurrent cut i hi
  have hiw : Witness n L cut (-1) i :=
    ⟨j,hj,hji,by simp only [neg_one_mul]; exact neg_pos.mpr (lt_of_le_of_ne (hle j hj hji) hjoff)⟩
  refine ⟨i,hi,hiw,?_⟩
  intro k hk hgood
  rcases hgood with rfl|hgood
  · exact hiw
  by_cases hki : k=i
  · simpa only [hki] using hiw
  refine ⟨i,hi,Ne.symm hki,?_⟩
  rw [intersection_swap n L hL k i hki]
  simp only [neg_one_mul]
  exact neg_pos.mpr (lt_of_le_of_ne (hle k hk hki) hgood)

/-- All blocked lines for the selected negative side pass through the
same cut intersection, excluding the cut and the witness line. -/
theorem blocked_line_on_pencil
    (n : Nat) (L : Nat→Line ℝ) (hL : NoParallel n L)
    (cut i : Fin n) (hi : i≠cut) (hiw : Witness n L cut (-1) i)
    (all : ∀ k : Fin n, k≠cut → k=i ∨
      affineEval (L cut) (intersection (L i) (L k))≠0 → Witness n L cut (-1) k)
    (k : Fin n) (hk : k≠cut) (blocked : ¬Witness n L cut (-1) k) :
    k≠i ∧ affineEval (L k) (intersection (L cut) (L i))=0 := by
  have hki : k≠i := by intro he; subst k; exact blocked hiw
  have hz : affineEval (L cut) (intersection (L i) (L k))=0 := by
    by_contra hne
    exact blocked (all k hk (Or.inr hne))
  have hid := noParallel_any n L hL i k i.isLt k.isLt (fun e => hki (Fin.ext e).symm)
  have he : intersection (L i) (L k)=intersection (L cut) (L i) :=
    ((intersection_eq_iff n L hL cut i hi.symm _).mpr ⟨hz,intersection_on_left _ _ hid⟩).symm
  exact ⟨hki,by rw [← he]; exact intersection_on_right _ _ hid⟩

#print axioms off_pencil_intersection
#print axioms common_side_except_pencil
#print axioms blocked_line_on_pencil
end Kobon.UpperOpenMathCutHalfplane
