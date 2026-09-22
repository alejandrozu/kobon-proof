import Kobon.BBLRealizedPencil
import Kobon.Reindex

/-! The analytic canonical arrangement is exactly the rotated perturbation
pencil used by the geometric persistence lemmas. -/
namespace Kobon.BBLCanonicalPencil
open Real BBLExtrema BBLIntersection BBLPersistence BBLCrossingCoordinates BBLRealizedPencil
  BBLAnalytic BBLGrid BBLGridCuts BBLPencilRegularity

noncomputable def direction (r : Nat) (δ : ℝ) (i : Nat) : Line ℝ :=
  ⟨slopeFactor δ (newIntercept r i),0,
    slopeFactor δ (newIntercept r i)*newIntercept r i⟩

theorem old_slopes_ne_zero (r : Nat) (ε : ℝ) (m : Nat → ℝ)
    (hp : NoParallel (4*r+1) (oldArrangement r ε m)) :
    ∀ j, j<4*r → m j≠0 := by
  intro j hj
  have hh := hp ⟨0,by omega⟩ ⟨j+1,by omega⟩ (show 0<j+1 by omega)
  simpa [oldArrangement,det,graphLine] using hh

theorem old_slopes_distinct (r : Nat) (ε : ℝ) (m : Nat → ℝ)
    (hp : NoParallel (4*r+1) (oldArrangement r ε m)) :
    ∀ i j : Fin (4*r), i<j → m i≠m j := by
  intro i j hij he
  have hh := hp ⟨i.val+1,by have := i.isLt; omega⟩
    ⟨j.val+1,by have := j.isLt; omega⟩ (show i.val+1<j.val+1 by exact Nat.add_lt_add_right hij 1)
  apply hh
  simp [oldArrangement,det,graphLine,he]

theorem old_intercepts_strict (r : Nat) (hr : 5≤r) (ε : ℝ)
    (hε0 : 0<ε) (hε : ε<tan (alpha r/2)) (i j : Nat)
    (hij : i<j) (hj : j<4*r) : oldIntercept r ε i<oldIntercept r ε j := by
  apply cut_increasing r hr ε hε0 hε <;> omega

theorem new_intercepts_strict (r : Nat) (hr : 5≤r) (i j : Nat)
    (hij : i<j) (hj : j<4*r) : newIntercept r i<newIntercept r j := by
  exact (beta_tan_strictMono r hr) (a := ⟨i,by omega⟩) (b := ⟨j,hj⟩) hij

theorem new_slopes_neg (r : Nat) (hr : 5≤r) (δ κ : ℝ) (hδ : 0<δ) (hκ : 0<κ)
    (i : Nat) (hi : i<2*r) : κ*slopeFactor δ (newIntercept r i)<0 := by
  exact mul_neg_of_pos_of_neg hκ (factor_neg δ _ hδ
    (beta_tan_negative r hr ⟨i,by omega⟩ hi))

theorem new_slopes_pos (r : Nat) (hr : 5≤r) (δ κ : ℝ) (hδ : 0<δ) (hκ : 0<κ)
    (i : Nat) (hi : 2*r ≤ i) (hi' : i<4*r) : 0<κ*slopeFactor δ (newIntercept r i) := by
  exact mul_pos hκ (factor_pos δ _ hδ (beta_tan_positive r hr ⟨i,hi'⟩ hi))

theorem perturb_direction (r : Nat) (δ κ : ℝ) (i : Nat) :
    perturb (graphLine 0 0) (direction r δ i) κ=pencilLine κ δ (newIntercept r i) := by
  simp [perturb,direction,graphLine,pencilLine,mul_assoc]

theorem arrangement_eq_rotate_pencil (r : Nat) (ε : ℝ) (m : Nat → ℝ) (δ κ : ℝ) :
    arrangement r ε m δ κ=Reindex.rotate (8*r+1)
      (pencilAppend (4*r+1) (oldArrangement r ε m) (direction r δ) 0 κ) := by
  funext j
  by_cases hj : j<4*r
  · simp [arrangement,hj,Reindex.rotate,Reindex.shift,show j+1<8*r+1 by omega,
      pencilAppend,show j+1<4*r+1 by omega,oldArrangement]
  by_cases hj' : j<8*r
  · have heq : j+1-(4*r+1)=j-4*r := by omega
    simp only [arrangement,if_neg hj,if_pos hj',Reindex.rotate,Reindex.shift,
      if_pos (show j+1<8*r+1 by omega),pencilAppend,
      if_neg (show ¬j+1<4*r+1 by omega),heq,oldArrangement,if_pos rfl]
    exact (perturb_direction r δ κ (j-4*r)).symm
  · simp [arrangement,hj,hj',Reindex.rotate,Reindex.shift,
      show ¬j+1<8*r+1 by omega,pencilAppend,oldArrangement]

#print axioms arrangement_eq_rotate_pencil
end Kobon.BBLCanonicalPencil
