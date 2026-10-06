import Kobon.OpenMathTranslationCounting

/-! Actual nonloss conditions for translation surgery.
An old zero side test is harmless when its derivative vanishes. Ordinary
supporting-line zeros always satisfy this condition. A geometric sufficient
condition keeps the moved line away from every multiple corner of every old
triangle, while allowing other concurrent points elsewhere in the arrangement.
-/
namespace Kobon.OpenMathTranslationRetention
open OpenMathTranslationGerms OpenMathTranslationCounting

theorem nonnegative_of_stationary_zero (a b : ℝ) (ha : 0≤a) (hz : a=0 → b=0) :
    Nonnegative a b := by
  by_cases h : a=0
  · exact Or.inr ⟨h,by rw [hz h]⟩
  · exact Or.inl (lt_of_le_of_ne ha (Ne.symm h))

theorem nonpositive_of_stationary_zero (a b : ℝ) (ha : a≤0) (hz : a=0 → b=0) :
    Nonpositive a b := by
  apply nonnegative_of_stationary_zero (-a) (-b) (by linarith)
  intro h
  have ha0 : a=0 := by linarith
  rw [hz ha0]
  simp

def StationaryZeros (n : ℕ) (L : ℕ → Line ℝ) (p : ℕ) : Prop :=
  ∀ t, TrianglePredicate n L t → ∀ r : Fin n,
    (orientedEval (L r) (L t.i) (L t.j)=0 → sideSlope L p r t.i t.j=0) ∧
    (orientedEval (L r) (L t.i) (L t.k)=0 → sideSlope L p r t.i t.k=0) ∧
    (orientedEval (L r) (L t.j) (L t.k)=0 → sideSlope L p r t.j t.k=0)

theorem old_triangle_germ (n : ℕ) (L : ℕ → Line ℝ) (p : ℕ)
    (hzero : StationaryZeros n L p) (t : Triple) (ht : TrianglePredicate n L t) :
    TriangleGerm n L p t := by
  rcases ht with ⟨hi,hj,hk,harea,hside⟩
  refine ⟨hi,hj,hk,Or.inl harea,?_⟩
  intro r
  have hz := hzero t ⟨hi,hj,hk,harea,hside⟩ r
  rcases hside r with ⟨ha,hb,hc⟩|⟨ha,hb,hc⟩
  · exact Or.inl ⟨nonnegative_of_stationary_zero _ _ ha hz.1,
      nonnegative_of_stationary_zero _ _ hb hz.2.1,
      nonnegative_of_stationary_zero _ _ hc hz.2.2⟩
  · exact Or.inr ⟨nonpositive_of_stationary_zero _ _ ha hz.1,
      nonpositive_of_stationary_zero _ _ hb hz.2.1,
      nonpositive_of_stationary_zero _ _ hc hz.2.2⟩

theorem source_subset_germs (n : ℕ) (L : ℕ → Line ℝ) (p : ℕ)
    (hzero : StationaryZeros n L p) : selected n L⊆germs n L p := by
  classical
  intro a ha
  simp only [selected,germs,Finset.mem_filter,Finset.mem_univ,true_and] at ha ⊢
  exact old_triangle_germ n L p hzero (tripleOf a) ha

theorem no_loss_count (n : ℕ) (L : ℕ → Line ℝ) (p : ℕ)
    (hzero : StationaryZeros n L p) :
    Small (fun ε=>count n L≤count n (translate L p ε)) := by
  have hc := Finset.card_le_card (source_subset_germs n L p hzero)
  apply (count_stable n L p).mono
  intro ε h
  rw [h]
  exact hc

def UntouchedCorner (p r i j : ℕ) : Prop :=
  r=i ∨ r=j ∨ (p≠r ∧ p≠i ∧ p≠j)

def TriangleCornersUntouched (n : ℕ) (L : ℕ → Line ℝ) (p : ℕ) : Prop :=
  ∀ t, TrianglePredicate n L t → ∀ r : Fin n,
    (orientedEval (L r) (L t.i) (L t.j)=0 → UntouchedCorner p r t.i t.j) ∧
    (orientedEval (L r) (L t.i) (L t.k)=0 → UntouchedCorner p r t.i t.k) ∧
    (orientedEval (L r) (L t.j) (L t.k)=0 → UntouchedCorner p r t.j t.k)

theorem sideSlope_self_left (L : ℕ → Line ℝ) (p i j : ℕ) :
    sideSlope L p i i j=0 := by
  unfold sideSlope orientedEval evalVertex vertex det translate
  split_ifs <;> ring

theorem sideSlope_self_right (L : ℕ → Line ℝ) (p i j : ℕ) :
    sideSlope L p j i j=0 := by
  unfold sideSlope orientedEval evalVertex vertex det translate
  split_ifs <;> ring

theorem sideSlope_untouched (L : ℕ → Line ℝ) (p r i j : ℕ)
    (h : UntouchedCorner p r i j) : sideSlope L p r i j=0 := by
  rcases h with hri|hrj|⟨hr,hi,hj⟩
  · subst r; exact sideSlope_self_left L p i j
  · subst r; exact sideSlope_self_right L p i j
  · simp [sideSlope,translate,Ne.symm hr,Ne.symm hi,Ne.symm hj]

theorem untouched_corners_stationary (n : ℕ) (L : ℕ → Line ℝ) (p : ℕ)
    (h : TriangleCornersUntouched n L p) : StationaryZeros n L p := by
  intro t ht r
  have hc := h t ht r
  exact ⟨fun hz=>sideSlope_untouched L p r t.i t.j (hc.1 hz),
    fun hz=>sideSlope_untouched L p r t.i t.k (hc.2.1 hz),
    fun hz=>sideSlope_untouched L p r t.j t.k (hc.2.2 hz)⟩

/-- One additional static birth, with all old triangles retained, gives +1. -/
theorem germ_gain_one (n : ℕ) (L : ℕ → Line ℝ) (p : ℕ)
    (hzero : StationaryZeros n L p) (t : Triple) (hg : TriangleGerm n L p t)
    (hnot : ¬TrianglePredicate n L t) : count n L+1≤germCount n L p := by
  classical
  have hi : t.i<n := by have h1:=hg.1; have h2:=hg.2.1; have h3:=hg.2.2.1; omega
  have hj : t.j<n := by have h1:=hg.2.1; have h2:=hg.2.2.1; omega
  let a : Indices n := (⟨t.i,hi⟩,⟨t.j,hj⟩,⟨t.k,hg.2.2.1⟩)
  have hta : tripleOf a=t := by cases t; rfl
  have haG : a∈germs n L p := by
    simp only [germs,Finset.mem_filter,Finset.mem_univ,true_and]
    exact hg
  have haS : a∉selected n L := by
    simp only [selected,Finset.mem_filter,Finset.mem_univ,true_and]
    rw [hta]
    exact hnot
  have hsub : insert a (selected n L)⊆germs n L p :=
    Finset.insert_subset haG (source_subset_germs n L p hzero)
  have hc := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem haS] at hc
  exact hc

theorem classical_gain_one (n : ℕ) (L : ℕ → Line ℝ) (p : ℕ)
    (hp : NoParallel n L) (hzero : StationaryZeros n L p)
    (t : Triple) (hg : TriangleGerm n L p t) (hnot : ¬TrianglePredicate n L t) :
    LowerBound n (count n L+1) :=
  classical_bound_of_germ_count n (count n L+1) L p hp
    (germ_gain_one n L p hzero t hg hnot)

#print axioms old_triangle_germ
#print axioms no_loss_count
#print axioms untouched_corners_stationary
#print axioms classical_gain_one
end Kobon.OpenMathTranslationRetention
