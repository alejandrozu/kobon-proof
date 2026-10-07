import Kobon.Projective

/-!
A finite projective change of chart removes parallel pairs while preserving
every certified bounded triangle.  Multiple intersections are retained.

The input requires distinct projective lines and nonparallel supporting pairs
for the listed triangles.  These local conditions are needed: the weak
polynomial triangle predicate alone is intended for a globally nonparallel
arrangement and must not be used unmodified for parallel supporting pairs.
-/
namespace Kobon.OpenMathParallelElimination
open scoped BigOperators

def PairDistinct (n : ℕ) (L : ℕ → Line ℝ) : Prop :=
  ∀ i j : Fin n, i < j →
    det (L i) (L j) ≠ 0 ∨ (vertex (L i) (L j)).1 ≠ 0 ∨
      (vertex (L i) (L j)).2.1 ≠ 0

def LocalNonparallel (L : ℕ → Line ℝ) (t : Triple) : Prop :=
  det (L t.i) (L t.j) ≠ 0 ∧ det (L t.i) (L t.k) ≠ 0 ∧
    det (L t.j) (L t.k) ≠ 0

noncomputable def slope (n : ℕ) (L : ℕ → Line ℝ) : ℝ :=
  1 + ∑ p : Fin n × Fin n,
    |(vertex (L p.1) (L p.2)).1 / (vertex (L p.1) (L p.2)).2.1|

theorem slope_pos (n : ℕ) (L : ℕ → Line ℝ) : 0 < slope n L := by
  have hs := Finset.sum_nonneg (s := (Finset.univ : Finset (Fin n × Fin n)))
    (fun p _ => abs_nonneg ((vertex (L p.1) (L p.2)).1 /
      (vertex (L p.1) (L p.2)).2.1))
  dsimp [slope]
  linarith

theorem ratio_lt_slope (n : ℕ) (L : ℕ → Line ℝ) (i j : Fin n) :
    |(vertex (L i) (L j)).1 / (vertex (L i) (L j)).2.1| < slope n L := by
  have hs := Finset.single_le_sum
    (s := (Finset.univ : Finset (Fin n × Fin n)))
    (f := fun p => |(vertex (L p.1) (L p.2)).1 /
      (vertex (L p.1) (L p.2)).2.1|)
    (fun p _ => abs_nonneg _) (Finset.mem_univ (i,j))
  dsimp [slope]
  linarith

theorem parallel_direction_nonzero (n : ℕ) (L : ℕ → Line ℝ)
    (hd : PairDistinct n L) (i j : Fin n) (hij : i < j)
    (hp : det (L i) (L j) = 0) :
    (vertex (L i) (L j)).1 + slope n L * (vertex (L i) (L j)).2.1 ≠ 0 := by
  intro he
  by_cases hy : (vertex (L i) (L j)).2.1 = 0
  · have hx : (vertex (L i) (L j)).1 = 0 := by simpa [hy] using he
    rcases hd i j hij with hh | hh | hh
    · exact hh hp
    · exact hh hx
    · exact hh hy
  · have hq : (vertex (L i) (L j)).1 / (vertex (L i) (L j)).2.1 =
        -(slope n L) := (div_eq_iff hy).mpr (by linarith)
    have hb := ratio_lt_slope n L i j
    rw [hq,abs_neg,abs_of_pos (slope_pos n L)] at hb
    exact (lt_irrefl _ hb)

noncomputable def vertexBound (n : ℕ) (L : ℕ → Line ℝ) : ℝ :=
  1 + ∑ p : Fin n × Fin n,
    |(intersection (L p.1) (L p.2)).1 +
      slope n L * (intersection (L p.1) (L p.2)).2|

theorem vertexBound_pos (n : ℕ) (L : ℕ → Line ℝ) : 0 < vertexBound n L := by
  have hs := Finset.sum_nonneg (s := (Finset.univ : Finset (Fin n × Fin n)))
    (fun p _ => abs_nonneg ((intersection (L p.1) (L p.2)).1 +
      slope n L * (intersection (L p.1) (L p.2)).2))
  dsimp [vertexBound]
  linarith

theorem projected_vertex_lt (n : ℕ) (L : ℕ → Line ℝ) (i j : Fin n) :
    (intersection (L i) (L j)).1 + slope n L * (intersection (L i) (L j)).2 <
      vertexBound n L := by
  have hs := Finset.single_le_sum
    (s := (Finset.univ : Finset (Fin n × Fin n)))
    (f := fun p => |(intersection (L p.1) (L p.2)).1 +
      slope n L * (intersection (L p.1) (L p.2)).2|)
    (fun p _ => abs_nonneg _) (Finset.mem_univ (i,j))
  have ha := le_abs_self ((intersection (L i) (L j)).1 +
    slope n L * (intersection (L i) (L j)).2)
  dsimp [vertexBound]
  linarith

def transform (s e : ℝ) (l : Line ℝ) : Line ℝ :=
  ⟨l.a-e*l.c,l.b-e*s*l.c,l.c⟩

noncomputable def epsilon (n : ℕ) (L : ℕ → Line ℝ) : ℝ :=
  1 / (2 * vertexBound n L)

theorem epsilon_pos (n : ℕ) (L : ℕ → Line ℝ) : 0 < epsilon n L := by
  dsimp [epsilon]
  exact one_div_pos.mpr (mul_pos (by norm_num) (vertexBound_pos n L))

noncomputable def factor (s e : ℝ) (l m : Line ℝ) : ℝ :=
  1-e*((intersection l m).1+s*(intersection l m).2)

theorem factor_pos (n : ℕ) (L : ℕ → Line ℝ) (i j : Fin n) :
    0 < factor (slope n L) (epsilon n L) (L i) (L j) := by
  have hb := vertexBound_pos n L
  have hv := projected_vertex_lt n L i j
  have hdouble : (intersection (L i) (L j)).1 +
      slope n L * (intersection (L i) (L j)).2 < 2 * vertexBound n L := by
    linarith
  have hdiv := (div_lt_one (show 0 < 2 * vertexBound n L by positivity)).mpr hdouble
  dsimp [factor,epsilon]
  have he : 1 / (2 * vertexBound n L) *
      ((intersection (L i) (L j)).1 + slope n L * (intersection (L i) (L j)).2) =
      ((intersection (L i) (L j)).1 + slope n L * (intersection (L i) (L j)).2) /
        (2 * vertexBound n L) := by ring
  rw [he]
  linarith

theorem det_transform (s e : ℝ) (l m : Line ℝ) :
    det (transform s e l) (transform s e m) =
      det l m-e*((vertex l m).1+s*(vertex l m).2.1) := by
  simp only [transform,det,vertex]
  ring

theorem det_transform_factor (s e : ℝ) (l m : Line ℝ) (hd : det l m ≠ 0) :
    det (transform s e l) (transform s e m) = det l m * factor s e l m := by
  rw [det_transform]
  dsimp [factor,intersection]
  field_simp

theorem eval_transform (s e : ℝ) (r l m : Line ℝ) :
    evalVertex (transform s e r) (transform s e l) (transform s e m) =
      evalVertex r l m := by
  simp only [transform,evalVertex,vertex,det]
  ring

theorem oriented_transform (s e : ℝ) (r l m : Line ℝ) (hd : det l m ≠ 0) :
    orientedEval (transform s e r) (transform s e l) (transform s e m) =
      orientedEval r l m * factor s e l m := by
  simp only [orientedEval,eval_transform,det_transform_factor s e l m hd]
  ring

noncomputable def arrangement (n : ℕ) (L : ℕ → Line ℝ) (i : ℕ) : Line ℝ :=
  transform (slope n L) (epsilon n L) (L i)

theorem noParallel (n : ℕ) (L : ℕ → Line ℝ) (hd : PairDistinct n L) :
    NoParallel n (arrangement n L) := by
  intro i j hij
  dsimp only [arrangement]
  by_cases hp : det (L i) (L j) = 0
  · rw [det_transform,hp,zero_sub]
    exact neg_ne_zero.mpr (mul_ne_zero (epsilon_pos n L).ne'
      (parallel_direction_nonzero n L hd i j hij hp))
  · rw [det_transform_factor _ _ _ _ hp]
    exact mul_ne_zero hp (factor_pos n L i j).ne'

theorem triangle_preserved (n : ℕ) (L : ℕ → Line ℝ) (t : Triple)
    (ht : TrianglePredicate n L t) (hp : LocalNonparallel L t) :
    TrianglePredicate n (arrangement n L) t := by
  rcases ht with ⟨hi,hj,hk,hd,hs⟩
  have hin : t.i < n := by omega
  have hjn : t.j < n := by omega
  have f1 := (factor_pos n L ⟨t.i,hin⟩ ⟨t.j,hjn⟩).le
  have f2 := (factor_pos n L ⟨t.i,hin⟩ ⟨t.k,hk⟩).le
  have f3 := (factor_pos n L ⟨t.j,hjn⟩ ⟨t.k,hk⟩).le
  refine ⟨hi,hj,hk,?_,?_⟩
  · simpa only [arrangement,eval_transform] using hd
  · intro r
    simp only [arrangement,oriented_transform _ _ _ _ _ hp.1,
      oriented_transform _ _ _ _ _ hp.2.1,oriented_transform _ _ _ _ _ hp.2.2]
    rcases hs r with hh | hh
    · exact Or.inl ⟨mul_nonneg hh.1 f1,mul_nonneg hh.2.1 f2,mul_nonneg hh.2.2 f3⟩
    · exact Or.inr ⟨mul_nonpos_of_nonpos_of_nonneg hh.1 f1,
        mul_nonpos_of_nonpos_of_nonneg hh.2.1 f2,
        mul_nonpos_of_nonpos_of_nonneg hh.2.2 f3⟩

def ArbitraryLowerBound (n T : ℕ) : Prop :=
  ∃ L : ℕ → Line ℝ, PairDistinct n L ∧
    ∃ ts : List Triple, ts.Nodup ∧
      (∀ t ∈ ts, TrianglePredicate n L t ∧ LocalNonparallel L t) ∧ T ≤ ts.length

theorem lowerBound_of_arbitrary (n T : ℕ) (h : ArbitraryLowerBound n T) :
    LowerBound n T := by
  rcases h with ⟨L,hd,ts,hn,ht,hc⟩
  exact ⟨arrangement n L,noParallel n L hd,ts,hn,
    fun t hh => triangle_preserved n L t (ht t hh).1 (ht t hh).2,hc⟩

theorem arbitrary_of_lowerBound (n T : ℕ) (h : LowerBound n T) :
    ArbitraryLowerBound n T := by
  rcases h with ⟨L,hp,ts,hn,ht,hc⟩
  refine ⟨L,fun i j hij => Or.inl (hp i j hij),ts,hn,?_,hc⟩
  intro t hh
  have hg := ht t hh
  have hi : t.i < n := by have := hg.1; have := hg.2.1; have := hg.2.2.1; omega
  have hj : t.j < n := by have := hg.2.1; have := hg.2.2.1; omega
  have hk := hg.2.2.1
  exact ⟨hg,hp ⟨t.i,hi⟩ ⟨t.j,hj⟩ hg.1,
    hp ⟨t.i,hi⟩ ⟨t.k,hk⟩ (by change t.i < t.k; exact Nat.lt_trans hg.1 hg.2.1),
    hp ⟨t.j,hj⟩ ⟨t.k,hk⟩ hg.2.1⟩

/-- Parallel pairs do not increase the extremal triangle count in this model. -/
theorem arbitrary_iff_lowerBound (n T : ℕ) :
    ArbitraryLowerBound n T ↔ LowerBound n T :=
  ⟨lowerBound_of_arbitrary n T,arbitrary_of_lowerBound n T⟩

#print axioms arbitrary_iff_lowerBound
end Kobon.OpenMathParallelElimination
