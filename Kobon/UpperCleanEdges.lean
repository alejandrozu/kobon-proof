import Kobon.UpperCleanHalfplane

/-!
# Actual bounded transverse segments on a common side of a clean line

The half-plane witnesses are converted to members of the actual consecutive
edge inventory. No bounded-segment existence or edge-enumeration hypothesis
is assumed. Triangle pairing and the final clean-line charge remain separate.
-/
namespace Kobon.UpperCleanEdges
open Cells UpperVertexBudget UpperTriangleIncidence UpperEdgeInventory
  UpperCleanHalfplane Finset

theorem consecutive_pair_mem
    (n : ℕ) (L : ℕ → Line ℝ) (i : Fin n)
    (a b : Fin (coordinates n L i).card) (hab : a.val+1=b.val) :
    {orderedPoint n L i a,orderedPoint n L i b}∈lineEdges n L i := by
  classical
  let k : Fin ((coordinates n L i).card-1) := ⟨a.val,by have := b.isLt; omega⟩
  refine mem_image.mpr ⟨k,mem_univ k,?_⟩
  have hka : (⟨k.val,by have := k.isLt; omega⟩ : Fin (coordinates n L i).card)=a := Fin.ext rfl
  have hkb : (⟨k.val+1,by have := k.isLt; omega⟩ : Fin (coordinates n L i).card)=b := Fin.ext hab
  simp only [intervalEdge,hka,hkb]

/-- A vertex on a line and a further vertex in an open half-plane determine
an actual consecutive segment from the first vertex into that half-plane. -/
theorem incident_positive_edge
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (i : Fin n) (cut : Line ℝ) (p q : Point)
    (hp : p∈onLine n L i) (hq : q∈onLine n L i)
    (hpzero : affineEval cut p=0) (hqpos : 0<affineEval cut q) :
    ∃ r : Point, r∈onLine n L i ∧ {p,r}∈lineEdges n L i ∧ 0<affineEval cut r := by
  classical
  obtain ⟨a,ha⟩ := orderedPoint_surjective n L hL hn i hp
  obtain ⟨b,hb⟩ := orderedPoint_surjective n L hL hn i hq
  rw [← ha] at hpzero ⊢
  rw [← hb] at hqpos
  have hne : a≠b := by intro he; rw [← he,hpzero] at hqpos; linarith
  rcases lt_or_gt_of_ne hne with hab|hba
  · let c : Fin (coordinates n L i).card := ⟨a.val+1,by have := b.isLt; have := Fin.lt_def.mp hab; omega⟩
    refine ⟨orderedPoint n L i c,orderedPoint_mem n L hL hn i c,
      consecutive_pair_mem n L i a c rfl,?_⟩
    by_cases hcb : c=b
    · simpa only [hcb] using hqpos
    · have hcb' : c<b := by change a.val+1<b.val; have := Fin.lt_def.mp hab; have : c.val≠b.val := fun h => hcb (Fin.ext h); dsimp [c] at this; omega
      obtain ⟨u,hu,hu1,hc⟩ := ordered_between n L i a b c
        (by change a.val<a.val+1; omega) hcb'
      rw [hc,affineEval_segment,hpzero,mul_zero,zero_add]
      exact mul_pos hu hqpos
  · let c : Fin (coordinates n L i).card := ⟨a.val-1,by have := a.isLt; omega⟩
    have hca : c.val+1=a.val := by have := Fin.lt_def.mp hba; dsimp [c]; omega
    refine ⟨orderedPoint n L i c,orderedPoint_mem n L hL hn i c,?_,?_⟩
    · rw [pair_comm]
      exact consecutive_pair_mem n L i c a hca
    · by_cases hcb : c=b
      · simpa only [hcb] using hqpos
      · have hbc : b<c := by change b.val<a.val-1; have := Fin.lt_def.mp hba; have : c.val≠b.val := fun h => hcb (Fin.ext h); dsimp [c] at this; omega
        obtain ⟨u,hu,hu1,hc⟩ := ordered_between n L i b a c hbc
          (by change a.val-1<a.val; have := Fin.lt_def.mp hba; omega)
        rw [hc,affineEval_segment,hpzero,mul_zero,add_zero]
        exact mul_pos (sub_pos.mpr hu1) hqpos

theorem incident_negative_edge
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (i : Fin n) (cut : Line ℝ) (p q : Point)
    (hp : p∈onLine n L i) (hq : q∈onLine n L i)
    (hpzero : affineEval cut p=0) (hqneg : affineEval cut q<0) :
    ∃ r : Point, r∈onLine n L i ∧ {p,r}∈lineEdges n L i ∧ affineEval cut r<0 := by
  let negcut : Line ℝ := ⟨-cut.a,-cut.b,-cut.c⟩
  have he : ∀ x, affineEval negcut x= -affineEval cut x := by intro x; dsimp [negcut,affineEval]; ring
  obtain ⟨r,hr,hedge,hpos⟩ := incident_positive_edge n L hL hn i negcut p q hp hq
    (by rw [he,hpzero]; simp) (by rw [he]; linarith)
  exact ⟨r,hr,hedge,by rw [he] at hpos; linarith⟩

/-- For one common open side of a clean line, every transverse crossing has
an incident member of the real consecutive-segment inventory on that side. -/
theorem common_bounded_side
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 3≤n)
    (line : Fin n) (hc : Clean n L line) :
    (∀ i : Fin n, i≠line → ∃ r : Point,
      {intersection (L line) (L i),r}∈lineEdges n L i ∧ 0<affineEval (L line) r) ∨
    (∀ i : Fin n, i≠line → ∃ r : Point,
      {intersection (L line) (L i),r}∈lineEdges n L i ∧ affineEval (L line) r<0) := by
  classical
  have hp : ∀ i : Fin n, i≠line → intersection (L line) (L i)∈onLine n L i := by
    intro i hi
    have hd := noParallel_any n L hL line i line.isLt i.isLt (fun h => hi (Fin.ext h).symm)
    exact mem_filter.mpr ⟨intersection_mem_vertices n L line i hi.symm,intersection_on_right _ _ hd⟩
  have hpzero : ∀ i : Fin n, i≠line → affineEval (L line) (intersection (L line) (L i))=0 := by
    intro i hi
    exact intersection_on_left _ _ (noParallel_any n L hL line i line.isLt i.isLt (fun h => hi (Fin.ext h).symm))
  have hq : ∀ i j : Fin n, i≠j → intersection (L i) (L j)∈onLine n L i := by
    intro i j hij
    exact mem_filter.mpr ⟨intersection_mem_vertices n L i j hij,intersection_on_left _ _
      (noParallel_any n L hL i j i.isLt j.isLt (fun h => hij (Fin.ext h)))⟩
  rcases common_halfplane n L hL hn line hc with hpos|hneg
  · left
    intro i hi
    obtain ⟨j,hjl,hji,hj⟩ := hpos i hi
    obtain ⟨r,hr,hedge,hpos⟩ := incident_positive_edge n L hL (by omega) i (L line)
      _ _ (hp i hi) (hq i j hji.symm) (hpzero i hi) hj
    exact ⟨r,hedge,hpos⟩
  · right
    intro i hi
    obtain ⟨j,hjl,hji,hj⟩ := hneg i hi
    obtain ⟨r,hr,hedge,hneg⟩ := incident_negative_edge n L hL (by omega) i (L line)
      _ _ (hp i hi) (hq i j hji.symm) (hpzero i hi) hj
    exact ⟨r,hedge,hneg⟩

#print axioms incident_positive_edge
#print axioms incident_negative_edge
#print axioms common_bounded_side
end Kobon.UpperCleanEdges
