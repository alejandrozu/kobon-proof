import Kobon.OpenMathTranslationRetention
import Kobon.Cells

/-! A safe actual triangle-birth operation at an isolated triple point.
Translating the largest indexed support creates a tiny triangular cell.
When the global old-triangle corner condition holds, every old triangle
survives and the count gains at least one. Other cores are allowed, but their
effects are covered by that global condition rather than ignored.
-/
namespace Kobon.OpenMathTripleBirth
open OpenMathTranslationGerms OpenMathTranslationCounting OpenMathTranslationRetention
open Cells

theorem nonnegative_or_nonpositive (a b : ℝ) : Nonnegative a b∨Nonpositive a b := by
  rcases lt_trichotomy a 0 with ha|ha|ha
  · exact Or.inr (Or.inl (by linarith))
  · subst a
    rcases le_total 0 b with hb|hb
    · exact Or.inl (Or.inr ⟨rfl,hb⟩)
    · exact Or.inr (Or.inr ⟨by simp,by linarith⟩)
  · exact Or.inl (Or.inl ha)

theorem oriented_self_left (l m : Line ℝ) : orientedEval l l m=0 := by
  dsimp [orientedEval,evalVertex,vertex,det]; ring

theorem oriented_self_right (l m : Line ℝ) : orientedEval m l m=0 := by
  dsimp [orientedEval,evalVertex,vertex,det]; ring

def SideGerm (L : ℕ → Line ℝ) (p r : ℕ) (t : Triple) : Prop :=
  (Nonnegative (orientedEval (L r) (L t.i) (L t.j)) (sideSlope L p r t.i t.j) ∧
   Nonnegative (orientedEval (L r) (L t.i) (L t.k)) (sideSlope L p r t.i t.k) ∧
   Nonnegative (orientedEval (L r) (L t.j) (L t.k)) (sideSlope L p r t.j t.k)) ∨
  (Nonpositive (orientedEval (L r) (L t.i) (L t.j)) (sideSlope L p r t.i t.j) ∧
   Nonpositive (orientedEval (L r) (L t.i) (L t.k)) (sideSlope L p r t.i t.k) ∧
   Nonpositive (orientedEval (L r) (L t.j) (L t.k)) (sideSlope L p r t.j t.k))

theorem support_side_germ (L : ℕ → Line ℝ) (p r : ℕ) (t : Triple)
    (h : r=t.i∨r=t.j∨r=t.k) : SideGerm L p r t := by
  rcases h with h|h|h
  · subst r
    simpa only [SideGerm,oriented_self_left,sideSlope_self_left,
      Nonnegative,Nonpositive,lt_self_iff_false,zero_eq_neg,neg_zero,le_refl,
      false_or,true_and] using nonnegative_or_nonpositive
      (orientedEval (L t.i) (L t.j) (L t.k)) (sideSlope L p t.i t.j t.k)
  · subst r
    simpa only [SideGerm,oriented_self_left,oriented_self_right,
      sideSlope_self_left,sideSlope_self_right,Nonnegative,Nonpositive,
      lt_self_iff_false,neg_zero,le_refl,false_or,true_and,and_true] using
      nonnegative_or_nonpositive (orientedEval (L t.j) (L t.i) (L t.k))
        (sideSlope L p t.j t.i t.k)
  · subst r
    simpa only [SideGerm,oriented_self_right,sideSlope_self_right,
      Nonnegative,Nonpositive,lt_self_iff_false,neg_zero,le_refl,
      false_or,true_and,and_true] using nonnegative_or_nonpositive
      (orientedEval (L t.k) (L t.i) (L t.j)) (sideSlope L p t.k t.i t.j)

theorem evalSlope_last (L : ℕ → Line ℝ) (i j k : ℕ) (hi : i≠k) (hj : j≠k) :
    evalSlope L k k i j= -det (L i) (L j) := by
  simp only [evalSlope,translate,if_pos,if_neg hi,if_neg hj]
  dsimp [evalVertex,vertex,det]
  ring

/-- The triple has precisely its three supporting lines through its center. -/
theorem tiny_triangle_germ (n : ℕ) (L : ℕ → Line ℝ) (i j k : Fin n)
    (hi : i<j) (hj : j<k) (hp : NoParallel n L)
    (hc : affineEval (L k) (intersection (L i) (L j))=0)
    (hother : ∀ r : Fin n, r≠i → r≠j → r≠k →
      affineEval (L r) (intersection (L i) (L j))≠0) :
    TriangleGerm n L k ⟨i,j,k⟩ := by
  have hij := hp i j hi
  have hik := hp i k (lt_trans hi hj)
  have hjk := hp j k hj
  let c := intersection (L i) (L j)
  have hci : affineEval (L i) c=0 := intersection_on_left _ _ hij
  have hcj : affineEval (L j) c=0 := intersection_on_right _ _ hij
  have hck : affineEval (L k) c=0 := hc
  have eik : c=intersection (L i) (L k) :=
    two_lines_two_points (L i) (L k) c _ hik hci
      (intersection_on_left _ _ hik) hck (intersection_on_right _ _ hik)
  have ejk : c=intersection (L j) (L k) :=
    two_lines_two_points (L j) (L k) c _ hjk hcj
      (intersection_on_left _ _ hjk) hck (intersection_on_right _ _ hjk)
  have hz : evalVertex (L k) (L i) (L j)=0 := by
    have he := eval_intersection (L k) (L i) (L j) hij
    rw [hc] at he
    exact (div_eq_zero_iff.mp he.symm).resolve_right hij
  refine ⟨hi,hj,k.isLt,Or.inr ?_,?_⟩
  · rw [evalSlope_last L i j k (by have hh:=lt_trans hi hj; exact ne_of_lt hh)
      (ne_of_lt hj)]
    exact neg_ne_zero.mpr hij
  · intro r
    by_cases hri : r=i
    · subst r
      exact support_side_germ L k i ⟨i,j,k⟩ (Or.inl rfl)
    by_cases hrj : r=j
    · subst r
      exact support_side_germ L k j ⟨i,j,k⟩ (Or.inr (Or.inl rfl))
    by_cases hrk : r=k
    · subst r
      exact support_side_germ L k k ⟨i,j,k⟩ (Or.inr (Or.inr rfl))
    have hrc := hother r hri hrj hrk
    have hs1 : orientedEval (L r) (L i) (L j)=affineEval (L r) c*(det (L i) (L j))^2 :=
      orientedEval_affine _ _ _ hij
    have hs2 : orientedEval (L r) (L i) (L k)=affineEval (L r) c*(det (L i) (L k))^2 := by
      rw [eik]
      exact orientedEval_affine _ _ _ hik
    have hs3 : orientedEval (L r) (L j) (L k)=affineEval (L r) c*(det (L j) (L k))^2 := by
      rw [ejk]
      exact orientedEval_affine _ _ _ hjk
    rcases lt_or_gt_of_ne hrc with hn|hpos
    · right
      refine ⟨Or.inl ?_,Or.inl ?_,Or.inl ?_⟩
      · rw [hs1]
        exact neg_pos.mpr (mul_neg_of_neg_of_pos hn (sq_pos_of_ne_zero hij))
      · rw [hs2]
        exact neg_pos.mpr (mul_neg_of_neg_of_pos hn (sq_pos_of_ne_zero hik))
      · rw [hs3]
        exact neg_pos.mpr (mul_neg_of_neg_of_pos hn (sq_pos_of_ne_zero hjk))
    · left
      refine ⟨Or.inl ?_,Or.inl ?_,Or.inl ?_⟩
      · rw [hs1]; exact mul_pos hpos (sq_pos_of_ne_zero hij)
      · rw [hs2]; exact mul_pos hpos (sq_pos_of_ne_zero hik)
      · rw [hs3]; exact mul_pos hpos (sq_pos_of_ne_zero hjk)

theorem triangle_free_triple_gain (n : ℕ) (L : ℕ → Line ℝ) (i j k : Fin n)
    (hi : i<j) (hj : j<k) (hp : NoParallel n L)
    (hc : affineEval (L k) (intersection (L i) (L j))=0)
    (hother : ∀ r : Fin n, r≠i → r≠j → r≠k →
      affineEval (L r) (intersection (L i) (L j))≠0)
    (hcorners : TriangleCornersUntouched n L k) : LowerBound n (count n L+1) := by
  have hg := tiny_triangle_germ n L i j k hi hj hp hc hother
  apply classical_gain_one n L k hp (untouched_corners_stationary n L k hcorners)
    ⟨i,j,k⟩ hg
  intro ht
  have he := eval_intersection (L k) (L i) (L j) (hp i j hi)
  rw [hc] at he
  exact ht.2.2.2.1 ((div_eq_zero_iff.mp he.symm).resolve_right (hp i j hi))

#print axioms support_side_germ
#print axioms tiny_triangle_germ
#print axioms triangle_free_triple_gain
end Kobon.OpenMathTripleBirth
