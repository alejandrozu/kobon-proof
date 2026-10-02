import Kobon.BBLTangentValues
import Kobon.BBLCrossingCoordinates
import Kobon.StrictLinearCertificate
import Mathlib.Tactic.FinCases

/-! A concrete obstruction to tangent-grid fitting. The ten prescribed
orientation signs below cannot be realized for any real central gap epsilon.
This is one case from the exact search, not an exhaustive classification. -/
namespace Kobon.BBLGridObstruction
open Real BBLTangentAlgebra BBLTangentValues BBLCrossingCoordinates BBLGridCuts BBLAnalytic
open scoped BigOperators
set_option maxHeartbeats 0

noncomputable def grid (t ε : ℝ) (j : Nat) : ℝ :=
  if j<9 then -value (9-j) t else if j=9 then -ε else
  if j=10 then ε else value (j-10) t

def support : Fin 10 → Triple := ![
  ⟨0,6,15⟩,
  ⟨0,7,13⟩,
  ⟨0,8,14⟩,
  ⟨0,13,19⟩,
  ⟨3,6,8⟩,
  ⟨3,11,15⟩,
  ⟨3,13,17⟩,
  ⟨7,11,13⟩,
  ⟨8,14,17⟩,
  ⟨8,15,19⟩]

def sign : Fin 10 → ℝ := ![-1,1,-1,1,1,-1,1,1,-1,-1]

noncomputable def weight (t : ℝ) : Fin 10 → ℝ := ![
  -20*t^3 + 120*t^2 + 300*t - 40,
  -8*t^3 + 24*t^2 + 96*t + 8,
  -45*t^3 + 205*t^2 + 555*t - 35,
  -16*t^3 - 6*t^2 + 40*t + 2,
  20*t^3 - 100*t^2 - 220*t + 100,
  20*t^3 - 120*t^2 - 220*t + 200,
  20*t^3 - 150*t^2 - 300*t + 130,
  -60*t^3 + 240*t^2 + 860*t + 320,
  -105*t^3 + 455*t^2 + 1275*t - 45,
  36*t^3 - 188*t^2 - 452*t + 124]

noncomputable def coefficient (a : Nat → ℝ) (i : Fin 10) (j : Fin 20) : ℝ :=
  sign i * (if j.val=(support i).i then a (support i).j-a (support i).k else
    if j.val=(support i).j then a (support i).k-a (support i).i else
    if j.val=(support i).k then a (support i).i-a (support i).j else 0)

theorem weight_positive (t : ℝ) (hl : (3:ℝ)/20<t) (hu : t<17/100) :
    ∀ i, 0<weight t i := by
  have ht : 0<t := by linarith
  have ht2 : t^2<(3:ℝ)/100 := by nlinarith [sq_nonneg (t-17/100)]
  have ht3 : 0<t^3 := pow_pos ht 3
  have ht3u : t^3<(1:ℝ)/200 := by
    have hh := mul_lt_mul_of_pos_right ht2 ht
    nlinarith
  intro i
  fin_cases i <;> norm_num [weight] <;> nlinarith [sq_nonneg t]

theorem column_zero (t ε : ℝ) (hq : quartic t=0) (j : Fin 20) :
    (∑ i : Fin 10, weight t i*coefficient (grid t ε) i j)=0 := by
  fin_cases j
  · norm_num [Fin.sum_univ_succ,weight,coefficient,sign,support,grid,value]
    unfold quartic at hq
    linear_combination (-129*t^2/10 + 119*t/5 - 299/10)*hq
  · norm_num [Fin.sum_univ_succ,weight,coefficient,sign,support,grid,value]
  · norm_num [Fin.sum_univ_succ,weight,coefficient,sign,support,grid,value]
  · norm_num [Fin.sum_univ_succ,weight,coefficient,sign,support,grid,value]
    unfold quartic at hq
    linear_combination (60*t - 40)*hq
  · norm_num [Fin.sum_univ_succ,weight,coefficient,sign,support,grid,value]
  · norm_num [Fin.sum_univ_succ,weight,coefficient,sign,support,grid,value]
  · norm_num [Fin.sum_univ_succ,weight,coefficient,sign,support,grid,value]
    unfold quartic at hq
    linear_combination (-22*t^2 + 128*t + 310)*hq
  · norm_num [Fin.sum_univ_succ,weight,coefficient,sign,support,grid,value]
    unfold quartic at hq
    linear_combination (-44*t^2 + 218*t + 500)*hq
  · norm_num [Fin.sum_univ_succ,weight,coefficient,sign,support,grid,value]
    unfold quartic at hq
    linear_combination (-24*t^2 + 285*t/2 + 609/2)*hq
  · norm_num [Fin.sum_univ_succ,weight,coefficient,sign,support,grid,value]
  · norm_num [Fin.sum_univ_succ,weight,coefficient,sign,support,grid,value]
  · norm_num [Fin.sum_univ_succ,weight,coefficient,sign,support,grid,value]
    unfold quartic at hq
    linear_combination (80*t^2 - 364*t - 964)*hq
  · norm_num [Fin.sum_univ_succ,weight,coefficient,sign,support,grid,value]
  · norm_num [Fin.sum_univ_succ,weight,coefficient,sign,support,grid,value]
    unfold quartic at hq
    linear_combination (32*t^2/5 + 571*t/5 + 1922/5)*hq
  · norm_num [Fin.sum_univ_succ,weight,coefficient,sign,support,grid,value]
    unfold quartic at hq
    linear_combination (45*t^2 - 515*t/2 - 145/2)*hq
  · norm_num [Fin.sum_univ_succ,weight,coefficient,sign,support,grid,value]
    unfold quartic at hq
    linear_combination (34*t^2 - 168*t - 496)*hq
  · norm_num [Fin.sum_univ_succ,weight,coefficient,sign,support,grid,value]
  · norm_num [Fin.sum_univ_succ,weight,coefficient,sign,support,grid,value]
    unfold quartic at hq
    linear_combination (-61*t^2/2 + 107*t - 31/2)*hq
  · norm_num [Fin.sum_univ_succ,weight,coefficient,sign,support,grid,value]
  · norm_num [Fin.sum_univ_succ,weight,coefficient,sign,support,grid,value]
    unfold quartic at hq
    linear_combination (-32*t^2 - 4*t + 119)*hq

theorem polynomial_grid_infeasible (t ε : ℝ) (hq : quartic t=0)
    (hl : (3:ℝ)/20<t) (hu : t<17/100) :
    ¬ ∃ v : Fin 20→ℝ, ∀ i : Fin 10,
      0<∑ j : Fin 20, coefficient (grid t ε) i j*v j := by
  apply StrictLinearCertificate.homogeneous_infeasible _ (weight t)
  · exact fun i => le_of_lt (weight_positive t hl hu i)
  · exact ⟨0,weight_positive t hl hu 0⟩
  · exact column_zero t ε hq

theorem grid_eq_actual (ε : ℝ) (j : Nat) (hj : j<20) :
    grid (tan (π/20)) ε j=oldIntercept 5 ε j := by
  interval_cases j
  · norm_num only [grid,oldIntercept,cut,leftAngle,rightAngle,alpha,
      Nat.cast_ofNat,Int.cast_ofNat,Int.cast_add,Int.cast_mul,
      Nat.reduceLT,Nat.reduceSub,Int.reduceLT,Int.reduceAdd,Int.reduceMul,
      Int.reduceSub,Int.reduceNeg,Int.reduceEq,ite_true,ite_false]
    rw [value_eq_tan 9 (by norm_num)]
    rw [←tan_neg]
    congr 1 <;> norm_num <;> ring
  · norm_num only [grid,oldIntercept,cut,leftAngle,rightAngle,alpha,
      Nat.cast_ofNat,Int.cast_ofNat,Int.cast_add,Int.cast_mul,
      Nat.reduceLT,Nat.reduceSub,Int.reduceLT,Int.reduceAdd,Int.reduceMul,
      Int.reduceSub,Int.reduceNeg,Int.reduceEq,ite_true,ite_false]
    rw [value_eq_tan 8 (by norm_num)]
    rw [←tan_neg]
    congr 1 <;> norm_num <;> ring
  · norm_num only [grid,oldIntercept,cut,leftAngle,rightAngle,alpha,
      Nat.cast_ofNat,Int.cast_ofNat,Int.cast_add,Int.cast_mul,
      Nat.reduceLT,Nat.reduceSub,Int.reduceLT,Int.reduceAdd,Int.reduceMul,
      Int.reduceSub,Int.reduceNeg,Int.reduceEq,ite_true,ite_false]
    rw [value_eq_tan 7 (by norm_num)]
    rw [←tan_neg]
    congr 1 <;> norm_num <;> ring
  · norm_num only [grid,oldIntercept,cut,leftAngle,rightAngle,alpha,
      Nat.cast_ofNat,Int.cast_ofNat,Int.cast_add,Int.cast_mul,
      Nat.reduceLT,Nat.reduceSub,Int.reduceLT,Int.reduceAdd,Int.reduceMul,
      Int.reduceSub,Int.reduceNeg,Int.reduceEq,ite_true,ite_false]
    rw [value_eq_tan 6 (by norm_num)]
    rw [←tan_neg]
    congr 1 <;> norm_num <;> ring
  · norm_num only [grid,oldIntercept,cut,leftAngle,rightAngle,alpha,
      Nat.cast_ofNat,Int.cast_ofNat,Int.cast_add,Int.cast_mul,
      Nat.reduceLT,Nat.reduceSub,Int.reduceLT,Int.reduceAdd,Int.reduceMul,
      Int.reduceSub,Int.reduceNeg,Int.reduceEq,ite_true,ite_false]
    rw [value_eq_tan 5 (by norm_num)]
    rw [←tan_neg]
    congr 1 <;> norm_num <;> ring
  · norm_num only [grid,oldIntercept,cut,leftAngle,rightAngle,alpha,
      Nat.cast_ofNat,Int.cast_ofNat,Int.cast_add,Int.cast_mul,
      Nat.reduceLT,Nat.reduceSub,Int.reduceLT,Int.reduceAdd,Int.reduceMul,
      Int.reduceSub,Int.reduceNeg,Int.reduceEq,ite_true,ite_false]
    rw [value_eq_tan 4 (by norm_num)]
    rw [←tan_neg]
    congr 1 <;> norm_num <;> ring
  · norm_num only [grid,oldIntercept,cut,leftAngle,rightAngle,alpha,
      Nat.cast_ofNat,Int.cast_ofNat,Int.cast_add,Int.cast_mul,
      Nat.reduceLT,Nat.reduceSub,Int.reduceLT,Int.reduceAdd,Int.reduceMul,
      Int.reduceSub,Int.reduceNeg,Int.reduceEq,ite_true,ite_false]
    rw [value_eq_tan 3 (by norm_num)]
    rw [←tan_neg]
    congr 1 <;> norm_num <;> ring
  · norm_num only [grid,oldIntercept,cut,leftAngle,rightAngle,alpha,
      Nat.cast_ofNat,Int.cast_ofNat,Int.cast_add,Int.cast_mul,
      Nat.reduceLT,Nat.reduceSub,Int.reduceLT,Int.reduceAdd,Int.reduceMul,
      Int.reduceSub,Int.reduceNeg,Int.reduceEq,ite_true,ite_false]
    rw [value_eq_tan 2 (by norm_num)]
    rw [←tan_neg]
    congr 1 <;> norm_num <;> ring
  · norm_num only [grid,oldIntercept,cut,leftAngle,rightAngle,alpha,
      Nat.cast_ofNat,Int.cast_ofNat,Int.cast_add,Int.cast_mul,
      Nat.reduceLT,Nat.reduceSub,Int.reduceLT,Int.reduceAdd,Int.reduceMul,
      Int.reduceSub,Int.reduceNeg,Int.reduceEq,ite_true,ite_false]
    rw [value_eq_tan 1 (by norm_num)]
    rw [←tan_neg]
    congr 1 <;> norm_num <;> ring
  · norm_num [grid,oldIntercept,cut]
  · norm_num [grid,oldIntercept,cut]
  · norm_num only [grid,oldIntercept,cut,leftAngle,rightAngle,alpha,
      Nat.cast_ofNat,Int.cast_ofNat,Int.cast_add,Int.cast_mul,
      Nat.reduceLT,Nat.reduceSub,Int.reduceLT,Int.reduceAdd,Int.reduceMul,
      Int.reduceSub,Int.reduceNeg,Int.reduceEq,ite_true,ite_false]
    rw [value_eq_tan 1 (by norm_num)]
    congr 1 <;> norm_num <;> ring
  · norm_num only [grid,oldIntercept,cut,leftAngle,rightAngle,alpha,
      Nat.cast_ofNat,Int.cast_ofNat,Int.cast_add,Int.cast_mul,
      Nat.reduceLT,Nat.reduceSub,Int.reduceLT,Int.reduceAdd,Int.reduceMul,
      Int.reduceSub,Int.reduceNeg,Int.reduceEq,ite_true,ite_false]
    rw [value_eq_tan 2 (by norm_num)]
    congr 1 <;> norm_num <;> ring
  · norm_num only [grid,oldIntercept,cut,leftAngle,rightAngle,alpha,
      Nat.cast_ofNat,Int.cast_ofNat,Int.cast_add,Int.cast_mul,
      Nat.reduceLT,Nat.reduceSub,Int.reduceLT,Int.reduceAdd,Int.reduceMul,
      Int.reduceSub,Int.reduceNeg,Int.reduceEq,ite_true,ite_false]
    rw [value_eq_tan 3 (by norm_num)]
    congr 1 <;> norm_num <;> ring
  · norm_num only [grid,oldIntercept,cut,leftAngle,rightAngle,alpha,
      Nat.cast_ofNat,Int.cast_ofNat,Int.cast_add,Int.cast_mul,
      Nat.reduceLT,Nat.reduceSub,Int.reduceLT,Int.reduceAdd,Int.reduceMul,
      Int.reduceSub,Int.reduceNeg,Int.reduceEq,ite_true,ite_false]
    rw [value_eq_tan 4 (by norm_num)]
    congr 1 <;> norm_num <;> ring
  · norm_num only [grid,oldIntercept,cut,leftAngle,rightAngle,alpha,
      Nat.cast_ofNat,Int.cast_ofNat,Int.cast_add,Int.cast_mul,
      Nat.reduceLT,Nat.reduceSub,Int.reduceLT,Int.reduceAdd,Int.reduceMul,
      Int.reduceSub,Int.reduceNeg,Int.reduceEq,ite_true,ite_false]
    rw [value_eq_tan 5 (by norm_num)]
    congr 1 <;> norm_num <;> ring
  · norm_num only [grid,oldIntercept,cut,leftAngle,rightAngle,alpha,
      Nat.cast_ofNat,Int.cast_ofNat,Int.cast_add,Int.cast_mul,
      Nat.reduceLT,Nat.reduceSub,Int.reduceLT,Int.reduceAdd,Int.reduceMul,
      Int.reduceSub,Int.reduceNeg,Int.reduceEq,ite_true,ite_false]
    rw [value_eq_tan 6 (by norm_num)]
    congr 1 <;> norm_num <;> ring
  · norm_num only [grid,oldIntercept,cut,leftAngle,rightAngle,alpha,
      Nat.cast_ofNat,Int.cast_ofNat,Int.cast_add,Int.cast_mul,
      Nat.reduceLT,Nat.reduceSub,Int.reduceLT,Int.reduceAdd,Int.reduceMul,
      Int.reduceSub,Int.reduceNeg,Int.reduceEq,ite_true,ite_false]
    rw [value_eq_tan 7 (by norm_num)]
    congr 1 <;> norm_num <;> ring
  · norm_num only [grid,oldIntercept,cut,leftAngle,rightAngle,alpha,
      Nat.cast_ofNat,Int.cast_ofNat,Int.cast_add,Int.cast_mul,
      Nat.reduceLT,Nat.reduceSub,Int.reduceLT,Int.reduceAdd,Int.reduceMul,
      Int.reduceSub,Int.reduceNeg,Int.reduceEq,ite_true,ite_false]
    rw [value_eq_tan 8 (by norm_num)]
    congr 1 <;> norm_num <;> ring
  · norm_num only [grid,oldIntercept,cut,leftAngle,rightAngle,alpha,
      Nat.cast_ofNat,Int.cast_ofNat,Int.cast_add,Int.cast_mul,
      Nat.reduceLT,Nat.reduceSub,Int.reduceLT,Int.reduceAdd,Int.reduceMul,
      Int.reduceSub,Int.reduceNeg,Int.reduceEq,ite_true,ite_false]
    rw [value_eq_tan 9 (by norm_num)]
    congr 1 <;> norm_num <;> ring

/-- No slope assignment realizes these ten orientation constraints on the
actual BBL grid, regardless of epsilon or of the sizes of the slopes. -/
theorem actual_grid_infeasible (ε : ℝ) :
    ¬ ∃ v : Fin 20→ℝ, ∀ i : Fin 10,
      0<∑ j : Fin 20, coefficient (oldIntercept 5 ε) i j*v j := by
  have he : coefficient (oldIntercept 5 ε)=coefficient (grid (tan (π/20)) ε) := by
    funext i j
    fin_cases i <;> simp only [coefficient,support,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_fin_one]
      <;> rw [grid_eq_actual ε _ (by norm_num),grid_eq_actual ε _ (by norm_num),
        grid_eq_actual ε _ (by norm_num)]
  rw [he]
  exact polynomial_grid_infeasible _ ε tan_quartic tan_root_interval.1 tan_root_interval.2

noncomputable def reciprocalLine (a v : Nat→ℝ) (i : Nat) : Line ℝ :=
  ⟨1,-v i,a i⟩

theorem coefficient_evaluation (a v : Nat→ℝ) (i : Fin 10) :
    (∑ j : Fin 20, coefficient a i j*v j.val)=
      sign i*evalVertex (reciprocalLine a v (support i).k)
        (reciprocalLine a v (support i).i) (reciprocalLine a v (support i).j) := by
  fin_cases i <;> norm_num [Fin.sum_univ_succ,coefficient,sign,support,
    reciprocalLine,evalVertex,vertex,det] <;> ring

/-- Geometric form: the specified ten determinant signs cannot occur among
real lines x-v_i*y=a_i on the actual tangent grid. -/
theorem actual_grid_orientation_impossible (ε : ℝ) :
    ¬ ∃ v : Nat→ℝ, ∀ i : Fin 10,
      0<sign i*evalVertex (reciprocalLine (oldIntercept 5 ε) v (support i).k)
        (reciprocalLine (oldIntercept 5 ε) v (support i).i)
        (reciprocalLine (oldIntercept 5 ε) v (support i).j) := by
  rintro ⟨v,hv⟩
  apply actual_grid_infeasible ε
  refine ⟨fun j => v j.val,?_⟩
  intro i
  rw [coefficient_evaluation]
  exact hv i

#print axioms actual_grid_orientation_impossible
#print axioms actual_grid_infeasible
end Kobon.BBLGridObstruction
