import Kobon.UpperCoreExtraction

/-!
# A common bounded side at a clean line

A clean line has only ordinary crossings. For at least three pairwise
nonparallel real lines, one of its open half-planes contains an intersection
on every transverse line. This is the geometric ingredient for a short
perfect-matching proof of the clean-line charging lemma. The conversion to
incident consecutive segments and their triangle-pairing map is separate.
-/
namespace Kobon.UpperCleanHalfplane
open Cells FanGeometry UpperVertexBudget Finset

def Clean (n : ℕ) (L : ℕ → Line ℝ) (line : Fin n) : Prop :=
  ∀ p∈onLine n L line, OrdinaryAt n L p

theorem transverse_intersection_off_clean
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L)
    (line i j : Fin n) (hc : Clean n L line)
    (hi : i≠line) (hj : j≠line) (hij : i≠j) :
    affineEval (L line) (intersection (L i) (L j))≠0 := by
  classical
  intro hz
  have hd := noParallel_any n L hL i j i.isLt j.isLt
    (fun h => hij (Fin.ext h))
  have hv : intersection (L i) (L j)∈vertices n L :=
    mem_image.mpr ⟨(i,j),mem_offDiag.mpr ⟨mem_univ _,mem_univ _,hij⟩,rfl⟩
  exact hij (ordinary_nonradial_unique n L _
    (hc _ (mem_filter.mpr ⟨hv,hz⟩)) line i j hz
    (intersection_on_left _ _ hd) (intersection_on_right _ _ hd) hi hj)

theorem intersection_swap
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L)
    (i j : Fin n) (hij : i≠j) :
    intersection (L i) (L j)=intersection (L j) (L i) := by
  have hd := noParallel_any n L hL j i j.isLt i.isLt
    (fun h => hij (Fin.ext h).symm)
  exact (intersection_eq_iff n L hL i j hij _).mpr
    ⟨intersection_on_right _ _ hd,intersection_on_left _ _ hd⟩

theorem third_index (n : ℕ) (hn : 3≤n) (line i : Fin n) :
    ∃ j : Fin n, j≠line ∧ j≠i := by
  classical
  by_contra h
  have hs : (univ : Finset (Fin n))⊆{line,i} := by
    intro j _
    by_cases hj : j=line
    · simp [hj]
    · have hji : j=i := by
        by_contra hji
        exact h ⟨j,hj,hji⟩
      simp [hji]
  have hcard := (card_le_card hs).trans (card_le_two (a:=line) (b:=i))
  simp only [card_univ,Fintype.card_fin] at hcard
  omega

/-- One open half-plane of a clean line contains an actual intersection on
every other line. Therefore every transverse line has a bounded incident
segment on this common side; that last consecutive-segment identification is
not bundled into this theorem. -/
theorem common_halfplane
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 3≤n)
    (line : Fin n) (hc : Clean n L line) :
    (∀ i : Fin n, i≠line → ∃ j : Fin n, j≠line ∧ j≠i ∧
      0<affineEval (L line) (intersection (L i) (L j))) ∨
    (∀ i : Fin n, i≠line → ∃ j : Fin n, j≠line ∧ j≠i ∧
      affineEval (L line) (intersection (L i) (L j))<0) := by
  classical
  by_cases hpos : ∀ i : Fin n, i≠line → ∃ j : Fin n, j≠line ∧ j≠i ∧
      0<affineEval (L line) (intersection (L i) (L j))
  · exact Or.inl hpos
  · right
    push Not at hpos
    obtain ⟨i,hi,hbad⟩ := hpos
    have hneg : ∀ j : Fin n, j≠line → j≠i →
        affineEval (L line) (intersection (L i) (L j))<0 := by
      intro j hj hji
      have hz := transverse_intersection_off_clean n L hL line i j hc hi hj hji.symm
      have hle := hbad j hj hji
      exact lt_of_le_of_ne hle hz
    intro k hk
    by_cases hki : k=i
    · subst k
      obtain ⟨j,hj,hji⟩ := third_index n hn line i
      exact ⟨j,hj,hji,hneg j hj hji⟩
    · refine ⟨i,hi,Ne.symm hki,?_⟩
      rw [intersection_swap n L hL k i hki]
      exact hneg k hk hki

/-- Distinct transverse lines give distinct crossings on a clean line. -/
theorem clean_crossings_injective
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L)
    (line : Fin n) (hc : Clean n L line) :
    Set.InjOn (fun i : Fin n => intersection (L line) (L i))
      {i | i≠line} := by
  intro i hi j hj he
  dsimp only at he
  have hdi := noParallel_any n L hL line i line.isLt i.isLt
    (fun h => hi (Fin.ext h).symm)
  have hdj := noParallel_any n L hL line j line.isLt j.isLt
    (fun h => hj (Fin.ext h).symm)
  have hv : intersection (L line) (L i)∈vertices n L :=
    mem_image.mpr ⟨(line,i),mem_offDiag.mpr
      ⟨mem_univ _,mem_univ _,hi.symm⟩,rfl⟩
  have hp := intersection_on_left (L line) (L i) hdi
  apply ordinary_nonradial_unique n L _ (hc _ (mem_filter.mpr ⟨hv,hp⟩))
    line i j hp (intersection_on_right _ _ hdi) _ hi hj
  rw [he]
  exact intersection_on_right _ _ hdj

/-- A triangle at an ordinary crossing of an indexed line must have a whole
side on that line: exactly one of the other two vertices lies on it. This
is the geometric pairing ingredient, not an assumed combinatorial matching. -/
theorem ordinary_vertex_pairs_on_line
    (n : ℕ) (L : ℕ → Line ℝ) (line : Fin n) (t : TriangleGeometry)
    (ht : UpperSharedIncidence.Indexed n L t)
    (ho : OrdinaryAt n L t.p) (hp : affineEval (L line) t.p=0) :
    (affineEval (L line) t.q=0 ∧ affineEval (L line) t.r≠0) ∨
    (affineEval (L line) t.r=0 ∧ affineEval (L line) t.q≠0) := by
  obtain ⟨a,b,c,ha,hb,hc⟩ := ht
  have hcb : c≠b := by
    intro he
    apply t.Bq
    rw [hb,← he,← hc]
    exact t.Cq
  by_cases hl : line=b
  · right
    simpa only [hl,← hb] using And.intro t.Br t.Bq
  · have hcl : c=line := ordinary_nonradial_unique n L t.p ho b c line
      (by simpa only [hb] using t.Bp)
      (by simpa only [hc] using t.Cp) hp hcb hl
    left
    simpa only [← hcl,← hc] using And.intro t.Cq t.Cr

theorem crossings_image
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (line : Fin n) :
    ((univ : Finset (Fin n)).erase line).image
      (fun i : Fin n => intersection (L line) (L i))=onLine n L line := by
  classical
  ext p
  constructor
  · intro hp
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hp
    have hil := (mem_erase.mp hi).1
    have hd := noParallel_any n L hL line i line.isLt i.isLt
      (fun h => hil (Fin.ext h).symm)
    exact mem_filter.mpr ⟨mem_image.mpr ⟨(line,i),mem_offDiag.mpr
      ⟨mem_univ _,mem_univ _,hil.symm⟩,rfl⟩,intersection_on_left _ _ hd⟩
  · intro hp
    obtain ⟨hv,hpL⟩ := mem_filter.mp hp
    obtain ⟨⟨i,j⟩,hij,he⟩ := mem_image.mp hv
    have hne := (mem_offDiag.mp hij).2.2
    have hboth := (intersection_eq_iff n L hL i j hne p).mp he
    by_cases hi : i=line
    · have hj : j≠line := by intro hj; exact hne (hi.trans hj.symm)
      exact mem_image.mpr ⟨j,mem_erase.mpr ⟨hj,mem_univ _⟩,
        (intersection_eq_iff n L hL line j hj.symm p).mpr ⟨hpL,hboth.2⟩⟩
    · exact mem_image.mpr ⟨i,mem_erase.mpr ⟨hi,mem_univ _⟩,
        (intersection_eq_iff n L hL line i (Ne.symm hi) p).mpr ⟨hpL,hboth.1⟩⟩

/-- The actual vertex set on a clean line has exactly n-1 elements. -/
theorem clean_crossing_card
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L)
    (line : Fin n) (hc : Clean n L line) :
    (onLine n L line).card=n-1 := by
  classical
  rw [← crossings_image n L hL line]
  rw [card_image_of_injOn]
  · simp
  · intro i hi j hj he
    exact clean_crossings_injective n L hL line hc
      (mem_erase.mp hi).1 (mem_erase.mp hj).1 he

/-- An even-order clean line cannot have its actual crossings partitioned
into two-element pairs. Geometrically, the pairs will be bases of triangles
on the common side. Extracting that partition from all chosen segments
having triangle degree one remains a separate finite-incidence obligation. -/
theorem clean_line_no_pair_partition
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L)
    (line : Fin n) (hc : Clean n L line) (heven : n%2=0)
    (pairs : Finset (Finset Point))
    (hpair : ∀ e∈pairs, e.card=2)
    (hdisj : (pairs : Set (Finset Point)).PairwiseDisjoint id)
    (hcover : pairs.biUnion id=onLine n L line) : False := by
  classical
  have hcount := card_biUnion hdisj
  rw [hcover,clean_crossing_card n L hL line hc] at hcount
  dsimp only [id_eq] at hcount
  have hs : (∑ e∈pairs, e.card)=pairs.card*2 := by
    calc
      (∑ e∈pairs, e.card)=∑ _e∈pairs, 2 := sum_congr rfl hpair
      _=pairs.card*2 := by simp
  rw [hs] at hcount
  have hpos : 0<n := Nat.zero_lt_of_lt line.isLt
  omega

#print axioms transverse_intersection_off_clean
#print axioms common_halfplane
#print axioms clean_crossings_injective
#print axioms ordinary_vertex_pairs_on_line
#print axioms clean_crossing_card
#print axioms clean_line_no_pair_partition
end Kobon.UpperCleanHalfplane
