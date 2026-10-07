import Kobon.OpenMathTripleBirth

/-!
Exact isolated-triple surgery at arbitrary order.
If the old arrangement has precisely one concurrent supporting triple, its
resolution has precisely one birth. Losses are determined by the actual
coefficient germs, giving T(ε)+lost=T(0)+1, not a half-plane sector guess.
-/
namespace Kobon.OpenMathIsolatedTripleResolution
open OpenMathTranslationGerms OpenMathTranslationCounting OpenMathTripleBirth

theorem nonnegative_initial (a b : ℝ) (h : Nonnegative a b) : 0≤a := by
  rcases h with h|⟨h,_⟩
  · exact le_of_lt h
  · rw [h]

theorem nonpositive_initial (a b : ℝ) (h : Nonpositive a b) : a≤0 := by
  have hh := nonnegative_initial (-a) (-b) h
  linarith

theorem germ_old_or_degenerate (n : ℕ) (L : ℕ → Line ℝ) (p : ℕ) (t : Triple)
    (hg : TriangleGerm n L p t) :
    TrianglePredicate n L t ∨ evalVertex (L t.k) (L t.i) (L t.j)=0 := by
  by_cases hz : evalVertex (L t.k) (L t.i) (L t.j)=0
  · exact Or.inr hz
  · left
    refine ⟨hg.1,hg.2.1,hg.2.2.1,hz,?_⟩
    intro r
    rcases hg.2.2.2.2 r with ⟨ha,hb,hc⟩|⟨ha,hb,hc⟩
    · exact Or.inl ⟨nonnegative_initial _ _ ha,nonnegative_initial _ _ hb,
        nonnegative_initial _ _ hc⟩
    · exact Or.inr ⟨nonpositive_initial _ _ ha,nonpositive_initial _ _ hb,
        nonpositive_initial _ _ hc⟩

def UniqueConcurrentTriple (n : ℕ) (L : ℕ → Line ℝ) (s : Triple) : Prop :=
  ∀ t, t.i<t.j → t.j<t.k → t.k<n →
    evalVertex (L t.k) (L t.i) (L t.j)=0 → t=s

theorem germ_old_or_unique_core (n : ℕ) (L : ℕ → Line ℝ) (p : ℕ)
    (s : Triple) (hu : UniqueConcurrentTriple n L s) (t : Triple)
    (hg : TriangleGerm n L p t) : TrianglePredicate n L t ∨ t=s := by
  rcases germ_old_or_degenerate n L p t hg with ht|hz
  · exact Or.inl ht
  · exact Or.inr (hu t hg.1 hg.2.1 hg.2.2.1 hz)

theorem unique_birth_set (n : ℕ) (L : ℕ → Line ℝ) (p : ℕ)
    (s : Triple) (hu : UniqueConcurrentTriple n L s)
    (hg : TriangleGerm n L p s) (hz : evalVertex (L s.k) (L s.i) (L s.j)=0) :
    ∃ a : Indices n, tripleOf a=s ∧ born n L p={a} := by
  classical
  have hi : s.i<n := by have h1:=hg.1; have h2:=hg.2.1; have h3:=hg.2.2.1; omega
  have hj : s.j<n := by have h1:=hg.2.1; have h2:=hg.2.2.1; omega
  let a : Indices n := (⟨s.i,hi⟩,⟨s.j,hj⟩,⟨s.k,hg.2.2.1⟩)
  have ha : tripleOf a=s := by cases s; rfl
  refine ⟨a,ha,?_⟩
  ext b
  simp only [born,Finset.mem_sdiff,selected,germs,Finset.mem_filter,
    Finset.mem_univ,true_and,Finset.mem_singleton]
  constructor
  · rintro ⟨hgb,hnot⟩
    rcases germ_old_or_unique_core n L p s hu (tripleOf b) hgb with ht|hs
    · exact False.elim (hnot ht)
    · exact tripleOf_injective n (hs.trans ha.symm)
  · intro hba
    subst b
    rw [ha]
    exact ⟨hg,fun ht=>ht.2.2.2.1 hz⟩

theorem unique_birth_card (n : ℕ) (L : ℕ → Line ℝ) (p : ℕ)
    (s : Triple) (hu : UniqueConcurrentTriple n L s)
    (hg : TriangleGerm n L p s) (hz : evalVertex (L s.k) (L s.i) (L s.j)=0) :
    (born n L p).card=1 := by
  rcases unique_birth_set n L p s hu hg hz with ⟨a,_,ha⟩
  rw [ha]
  simp

/-- Exactly one birth; every loss is certified by the global coefficient tests. -/
theorem isolated_resolution_identity (n : ℕ) (L : ℕ → Line ℝ) (i j k : Fin n)
    (hi : i<j) (hj : j<k) (hp : NoParallel n L)
    (hc : affineEval (L k) (intersection (L i) (L j))=0)
    (hother : ∀ r : Fin n, r≠i → r≠j → r≠k →
      affineEval (L r) (intersection (L i) (L j))≠0)
    (hu : UniqueConcurrentTriple n L ⟨i,j,k⟩) :
    Small (fun ε=>count n (translate L k ε)+(lost n L k).card=count n L+1) := by
  have hg := tiny_triangle_germ n L i j k hi hj hp hc hother
  have hz : evalVertex (L k) (L i) (L j)=0 := by
    have he := eval_intersection (L k) (L i) (L j) (hp i j hi)
    rw [hc] at he
    exact (div_eq_zero_iff.mp he.symm).resolve_right (hp i j hi)
  have hb := unique_birth_card n L k ⟨i,j,k⟩ hu hg hz
  simpa only [hb] using translated_birth_loss_identity n L k

#print axioms germ_old_or_degenerate
#print axioms unique_birth_card
#print axioms isolated_resolution_identity
end Kobon.OpenMathIsolatedTripleResolution
