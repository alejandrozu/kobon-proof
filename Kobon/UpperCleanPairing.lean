import Kobon.UpperCoreExtraction

/-!
# Uniqueness of the selected transverse edge

Two actual consecutive segments from one vertex into the same open side of
a line must coincide. This supplies the geometric uniqueness map needed in
the clean-line perfect-matching argument; the final cover is not assumed to
have been extracted here.
-/
namespace Kobon.UpperCleanPairing
open Cells UpperVertexBudget UpperEdgeInventory Finset

theorem pair_indices_consecutive
    (n : ℕ) (L : ℕ → Line ℝ) (i : Fin n)
    (a b : Fin (coordinates n L i).card)
    (he : {orderedPoint n L i a,orderedPoint n L i b}∈lineEdges n L i) :
    a.val+1=b.val ∨ b.val+1=a.val := by
  classical
  obtain ⟨k,hk,hke⟩ := mem_image.mp he
  have hcard := intervalEdge_card n L i k
  rw [hke] at hcard
  have hne : a.val≠b.val := by
    intro h
    have hab : a=b := Fin.ext h
    simp [hab] at hcard
  have ha : orderedPoint n L i a∈intervalEdge n L i k := by rw [hke]; simp
  have hb : orderedPoint n L i b∈intervalEdge n L i k := by rw [hke]; simp
  simp only [intervalEdge,mem_insert,mem_singleton] at ha hb
  have hva : a.val=k.val ∨ a.val=k.val+1 := by
    rcases ha with h|h
    · exact Or.inl (congrArg Fin.val (orderedPoint_injective n L i h))
    · exact Or.inr (congrArg Fin.val (orderedPoint_injective n L i h))
  have hvb : b.val=k.val ∨ b.val=k.val+1 := by
    rcases hb with h|h
    · exact Or.inl (congrArg Fin.val (orderedPoint_injective n L i h))
    · exact Or.inr (congrArg Fin.val (orderedPoint_injective n L i h))
  omega

/-- The selected actual elementary segment on a prescribed positive side
is unique. This is derived from consecutive indices and affine signs. -/
theorem incident_positive_unique
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (i : Fin n) (cut : Line ℝ) (p q r : Point)
    (hp : p∈onLine n L i) (hq : q∈onLine n L i) (hr : r∈onLine n L i)
    (heq : {p,q}∈lineEdges n L i) (her : {p,r}∈lineEdges n L i)
    (hpzero : affineEval cut p=0)
    (hqpos : 0<affineEval cut q) (hrpos : 0<affineEval cut r) : q=r := by
  classical
  obtain ⟨a,ha⟩ := orderedPoint_surjective n L hL hn i hp
  obtain ⟨b,hb⟩ := orderedPoint_surjective n L hL hn i hq
  obtain ⟨c,hc⟩ := orderedPoint_surjective n L hL hn i hr
  rw [← ha,← hb] at heq
  rw [← ha,← hc] at her
  rw [← ha] at hpzero
  rw [← hb] at hqpos
  rw [← hc] at hrpos
  have hab := pair_indices_consecutive n L i a b heq
  have hac := pair_indices_consecutive n L i a c her
  by_cases hbc : b=c
  · exact hb.symm.trans ((congrArg (orderedPoint n L i) hbc).trans hc)
  · have hbcval : b.val≠c.val := fun h => hbc (Fin.ext h)
    have horder : (b<a ∧ a<c) ∨ (c<a ∧ a<b) := by
      simp only [Fin.lt_def]
      omega
    rcases horder with ⟨hba,hac⟩|⟨hca,hab⟩
    · obtain ⟨u,hu,hu1,he⟩ := ordered_between n L i b c a hba hac
      rw [he,affineEval_segment] at hpzero
      have h1 := mul_pos (sub_pos.mpr hu1) hqpos
      have h2 := mul_pos hu hrpos
      linarith
    · obtain ⟨u,hu,hu1,he⟩ := ordered_between n L i c b a hca hab
      rw [he,affineEval_segment] at hpzero
      have h1 := mul_pos (sub_pos.mpr hu1) hrpos
      have h2 := mul_pos hu hqpos
      linarith

theorem incident_negative_unique
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (i : Fin n) (cut : Line ℝ) (p q r : Point)
    (hp : p∈onLine n L i) (hq : q∈onLine n L i) (hr : r∈onLine n L i)
    (heq : {p,q}∈lineEdges n L i) (her : {p,r}∈lineEdges n L i)
    (hpzero : affineEval cut p=0)
    (hqneg : affineEval cut q<0) (hrneg : affineEval cut r<0) : q=r := by
  let negcut : Line ℝ := ⟨-cut.a,-cut.b,-cut.c⟩
  have he : ∀ x, affineEval negcut x= -affineEval cut x := by intro x; dsimp [negcut,affineEval]; ring
  exact incident_positive_unique n L hL hn i negcut p q r hp hq hr heq her
    (by rw [he,hpzero]; simp) (by rw [he]; linarith) (by rw [he]; linarith)

#print axioms pair_indices_consecutive
#print axioms incident_positive_unique
#print axioms incident_negative_unique
end Kobon.UpperCleanPairing
