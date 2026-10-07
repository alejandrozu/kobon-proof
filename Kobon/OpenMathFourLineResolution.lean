import Kobon.Cells
import Kobon.Simple
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-!
An exact four-line diagnostic for a half-plane desingularization formula.
The original two triangles lie strictly in x-y>0. Moving y=x to y=x+ε,
for every 0<ε<1, leaves exactly two triangles and moves into x-y<0.
No general formula from the audited preprint is assumed.
-/
namespace Kobon.OpenMathFourLineResolution
open Cells

def oldInt : ℕ → Line ℤ
  | 0 => ⟨0,1,0⟩
  | 1 => ⟨1,-1,0⟩
  | 2 => ⟨1,1,0⟩
  | _ => ⟨2,1,2⟩

def old (i : ℕ) : Line ℝ := liftLine (oldInt i)

def moved (ε : ℝ) : ℕ → Line ℝ
  | 0 => ⟨0,1,0⟩
  | 1 => ⟨1,-1,-ε⟩
  | 2 => ⟨1,1,0⟩
  | _ => ⟨2,1,2⟩

def all4 : Finset Triple := {⟨0,1,2⟩,⟨0,1,3⟩,⟨0,2,3⟩,⟨1,2,3⟩}
noncomputable def triangles (L : ℕ → Line ℝ) : Finset Triple := by
  classical
  exact all4.filter (TrianglePredicate 4 L)

theorem ordered_cases (t : Triple) (hi : t.i<t.j) (hj : t.j<t.k) (hk : t.k<4) :
    t=⟨0,1,2⟩ ∨ t=⟨0,1,3⟩ ∨ t=⟨0,2,3⟩ ∨ t=⟨1,2,3⟩ := by
  rcases t with ⟨i,j,k⟩
  simp only [Triple.mk.injEq]
  dsimp at hi hj hk
  omega

theorem old_triangle_iff (t : Triple) :
    TrianglePredicate 4 old t ↔ t=⟨0,1,3⟩ ∨ t=⟨0,2,3⟩ := by
  constructor
  · intro ht
    have hc := ordered_cases t ht.1 ht.2.1 ht.2.2.1
    rcases hc with rfl|rfl|rfl|rfl
    · norm_num [TrianglePredicate,old,oldInt,liftLine,evalVertex,vertex,det] at ht
    · exact Or.inl rfl
    · exact Or.inr rfl
    · have hh := ht.2.2.2.2 ⟨0,by decide⟩
      norm_num [old,oldInt,liftLine,orientedEval,evalVertex,vertex,det] at hh
  · rintro (rfl|rfl)
    all_goals refine ⟨by decide,by decide,by decide,?_,?_⟩
    all_goals try norm_num [old,oldInt,liftLine,evalVertex,vertex,det]
    all_goals intro r; fin_cases r <;>
      norm_num [old,oldInt,liftLine,orientedEval,evalVertex,vertex,det]

theorem moved_triangle_iff (ε : ℝ) (he : 0<ε) (hsmall : ε<1) (t : Triple) :
    TrianglePredicate 4 (moved ε) t ↔ t=⟨0,1,2⟩ ∨ t=⟨0,2,3⟩ := by
  constructor
  · intro ht
    have hc := ordered_cases t ht.1 ht.2.1 ht.2.2.1
    rcases hc with rfl|rfl|rfl|rfl
    · exact Or.inl rfl
    · have hh := ht.2.2.2.2 ⟨2,by decide⟩
      norm_num [moved,orientedEval,evalVertex,vertex,det] at hh
      nlinarith
    · exact Or.inr rfl
    · have hh := ht.2.2.2.2 ⟨0,by decide⟩
      norm_num [moved,orientedEval,evalVertex,vertex,det] at hh
      nlinarith
  · rintro (rfl|rfl)
    all_goals refine ⟨by decide,by decide,by decide,?_,?_⟩
    · norm_num [moved,evalVertex,vertex,det]; linarith
    · intro r; fin_cases r
      · refine Or.inl ⟨?_,?_,?_⟩ <;>
          norm_num [moved,orientedEval,evalVertex,vertex,det] <;> linarith
      · refine Or.inl ⟨?_,?_,?_⟩ <;>
          norm_num [moved,orientedEval,evalVertex,vertex,det] <;> linarith
      · refine Or.inr ⟨?_,?_,?_⟩ <;>
          norm_num [moved,orientedEval,evalVertex,vertex,det] <;> linarith
      · refine Or.inr ⟨?_,?_,?_⟩ <;>
          norm_num [moved,orientedEval,evalVertex,vertex,det] <;> linarith
    · norm_num [moved,evalVertex,vertex,det]
    · intro r; fin_cases r
      · refine Or.inr ⟨?_,?_,?_⟩ <;>
          norm_num [moved,orientedEval,evalVertex,vertex,det] <;> linarith
      · refine Or.inl ⟨?_,?_,?_⟩ <;>
          norm_num [moved,orientedEval,evalVertex,vertex,det] <;> linarith
      · refine Or.inl ⟨?_,?_,?_⟩ <;>
          norm_num [moved,orientedEval,evalVertex,vertex,det] <;> linarith
      · refine Or.inr ⟨?_,?_,?_⟩ <;>
          norm_num [moved,orientedEval,evalVertex,vertex,det] <;> linarith

theorem old_no_parallel : NoParallel 4 old := by
  exact noParallel_lift 4 oldInt (by decide)

theorem old_unique_triple (t : Triple) (hi : t.i<t.j) (hj : t.j<t.k) (hk : t.k<4) :
    evalVertex (old t.k) (old t.i) (old t.j)=0 ↔ t=⟨0,1,2⟩ := by
  rcases ordered_cases t hi hj hk with rfl|rfl|rfl|rfl <;>
    norm_num [old,oldInt,liftLine,evalVertex,vertex,det,Triple.mk.injEq]

theorem moved_no_parallel (ε : ℝ) : NoParallel 4 (moved ε) := by
  intro i j hij
  change i.val<j.val at hij
  fin_cases i <;> fin_cases j
  all_goals norm_num at hij
  all_goals norm_num [moved,det]

theorem moved_no_concurrent (ε : ℝ) (he : 0<ε) (hsmall : ε<1) :
    NoConcurrent 4 (moved ε) := by
  intro i j k hij hjk
  change i.val<j.val at hij
  change j.val<k.val at hjk
  fin_cases i <;> fin_cases j <;> fin_cases k
  all_goals norm_num at hij
  all_goals norm_num at hjk
  all_goals norm_num [moved,evalVertex,vertex,det]
  all_goals linarith

theorem triangle_set_complete (L : ℕ → Line ℝ) (t : Triple) :
    t∈triangles L ↔ TrianglePredicate 4 L t := by
  classical
  simp only [triangles,Finset.mem_filter]
  constructor
  · exact fun h => h.2
  · intro ht
    refine ⟨?_,ht⟩
    rcases ordered_cases t ht.1 ht.2.1 ht.2.2.1 with rfl|rfl|rfl|rfl <;>
      simp [all4]

theorem old_count : (triangles old).card=2 := by
  classical
  have hs : triangles old={⟨0,1,3⟩,⟨0,2,3⟩} := by
    ext t
    simp only [triangle_set_complete,old_triangle_iff,Finset.mem_insert,
      Finset.mem_singleton]
  rw [hs]
  decide

theorem moved_count (ε : ℝ) (he : 0<ε) (hsmall : ε<1) :
    (triangles (moved ε)).card=2 := by
  classical
  have hs : triangles (moved ε)={⟨0,1,2⟩,⟨0,2,3⟩} := by
    ext t
    simp only [triangle_set_complete,moved_triangle_iff ε he hsmall,
      Finset.mem_insert,Finset.mem_singleton]
  rw [hs]
  decide

noncomputable def interior (L : ℕ → Line ℝ) (t : Triple) : Set Point :=
  OpenTriangle (intersection (L t.i) (L t.j))
    (intersection (L t.i) (L t.k)) (intersection (L t.j) (L t.k))

theorem old_interiors_positive (t : Triple) (ht : TrianglePredicate 4 old t)
    (p : Point) (hp : p∈interior old t) : 0<affineEval (old 1) p := by
  rcases (old_triangle_iff t).mp ht with rfl|rfl
  all_goals rcases hp with ⟨u,v,w,hu,hv,hw,hs,rfl⟩
  all_goals rw [affineEval_barycenter _ _ _ _ _ _ _ hs]
  all_goals norm_num [old,oldInt,liftLine,intersection,vertex,det,affineEval]
  all_goals positivity

noncomputable def negativeTriangles : Finset Triple := by
  classical
  exact (triangles old).filter fun t => ∀ p∈interior old t, affineEval (old 1) p<0

theorem negative_count_zero : negativeTriangles.card=0 := by
  classical
  have hs : negativeTriangles=∅ := by
    ext t
    simp only [Finset.notMem_empty,iff_false]
    intro ht
    rcases Finset.mem_filter.mp ht with ⟨ht,hneg⟩
    have htri := (triangle_set_complete old t).mp ht
    let p := barycenter (intersection (old t.i) (old t.j))
      (intersection (old t.i) (old t.k)) (intersection (old t.j) (old t.k))
      (1/3) (1/3) (1/3)
    have hp : p∈interior old t := ⟨1/3,1/3,1/3,by norm_num,by norm_num,
      by norm_num,by norm_num,rfl⟩
    exact (not_lt_of_gt (old_interiors_positive t htri p hp)) (hneg p hp)
  simp [hs]

theorem moved_line_negative_level (ε : ℝ) (p : Point)
    (hp : affineEval (moved ε 1) p=0) : affineEval (old 1) p=-ε := by
  norm_num [moved,old,oldInt,liftLine,affineEval] at hp ⊢
  linarith

/-- The claimed half-plane count formula fails for arbitrarily small motions. -/
theorem halfplane_yield_fails (ε : ℝ) (he : 0<ε) (hsmall : ε<1) :
    (triangles (moved ε)).card≠(triangles old).card+1-negativeTriangles.card := by
  rw [moved_count ε he hsmall,old_count,negative_count_zero]
  decide

#print axioms moved_triangle_iff
#print axioms old_unique_triple
#print axioms old_interiors_positive
#print axioms negative_count_zero
#print axioms halfplane_yield_fails
end Kobon.OpenMathFourLineResolution
