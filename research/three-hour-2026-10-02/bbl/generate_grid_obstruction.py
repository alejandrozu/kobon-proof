"""Generate a kernel-checkable certificate for the actual tangent grid.

This is one fixed ten-sign obstruction, not a classification completeness claim.
"""
from pathlib import Path
import json,sys
ROOT=Path(__file__).resolve().parents[3]
sys.path.insert(0,str(ROOT/'work/python-deps'))
import sympy as s
t=s.symbols('t')
data=json.loads((ROOT/'research/three-hour-2026-10-02/constructions/grid21-obstruction/representative-238.json').read_text(encoding='utf-8'))
def poly(cs):return sum(s.Rational(c)*t**j for j,c in enumerate(reversed(cs)))
def lean(z):return str(s.expand(z)).replace('**','^')
weights=[poly(w[0]['coefficient']) for w in data['weights']]
lines=['import Kobon.BBLTangentValues','import Kobon.BBLCrossingCoordinates','import Kobon.StrictLinearCertificate','import Mathlib.Tactic.FinCases','','/-! A concrete obstruction to tangent-grid fitting. The ten prescribed','orientation signs below cannot be realized for any real central gap epsilon.','This is one case from the exact search, not an exhaustive classification. -/','namespace Kobon.BBLGridObstruction','open Real BBLTangentAlgebra BBLTangentValues BBLCrossingCoordinates BBLGridCuts BBLAnalytic','open scoped BigOperators','set_option maxHeartbeats 0','','noncomputable def grid (t ε : ℝ) (j : Nat) : ℝ :=','  if j<9 then -value (9-j) t else if j=9 then -ε else','  if j=10 then ε else value (j-10) t','','def support : Fin 10 → Triple := ![']
lines += [f'  ⟨{i},{j},{k}⟩'+(',' if z<9 else ']') for z,(_,i,j,k,sgn) in enumerate(data['support'])]
lines += ['','def sign : Fin 10 → ℝ := !['+','.join(str(z[-1]) for z in data['support'])+']','','noncomputable def weight (t : ℝ) : Fin 10 → ℝ := ![']
lines += ['  '+lean(w)+(',' if k<9 else ']') for k,w in enumerate(weights)]
lines += ['','noncomputable def coefficient (a : Nat → ℝ) (i : Fin 10) (j : Fin 20) : ℝ :=','  sign i * (if j.val=(support i).i then a (support i).j-a (support i).k else','    if j.val=(support i).j then a (support i).k-a (support i).i else','    if j.val=(support i).k then a (support i).i-a (support i).j else 0)','','theorem weight_positive (t : ℝ) (hl : (3:ℝ)/20<t) (hu : t<17/100) :','    ∀ i, 0<weight t i := by','  have ht : 0<t := by linarith','  have ht2 : t^2<(3:ℝ)/100 := by nlinarith [sq_nonneg (t-17/100)]','  have ht3 : 0<t^3 := pow_pos ht 3','  have ht3u : t^3<(1:ℝ)/200 := by','    have hh := mul_lt_mul_of_pos_right ht2 ht','    nlinarith','  intro i','  fin_cases i <;> norm_num [weight] <;> nlinarith [sq_nonneg t]','','theorem column_zero (t ε : ℝ) (hq : quartic t=0) (j : Fin 20) :','    (∑ i : Fin 10, weight t i*coefficient (grid t ε) i j)=0 := by','  fin_cases j']
for q in data['weighted_column_quotients_by_quartic']:
    lines += ['  · norm_num [Fin.sum_univ_succ,weight,coefficient,sign,support,grid,value]','    unfold quartic at hq',f'    linear_combination ({lean(s.sympify(q))})*hq'] if q!='0' else ['  · norm_num [Fin.sum_univ_succ,weight,coefficient,sign,support,grid,value]']
lines += ['','theorem polynomial_grid_infeasible (t ε : ℝ) (hq : quartic t=0)','    (hl : (3:ℝ)/20<t) (hu : t<17/100) :','    ¬ ∃ v : Fin 20→ℝ, ∀ i : Fin 10,','      0<∑ j : Fin 20, coefficient (grid t ε) i j*v j := by','  apply StrictLinearCertificate.homogeneous_infeasible _ (weight t)','  · exact fun i => le_of_lt (weight_positive t hl hu i)','  · exact ⟨0,weight_positive t hl hu 0⟩','  · exact column_zero t ε hq','','theorem grid_eq_actual (ε : ℝ) (j : Nat) (hj : j<20) :','    grid (tan (π/20)) ε j=oldIntercept 5 ε j := by','  interval_cases j']
for j in range(20):
    if j in [9,10]:
        lines += ['  · norm_num [grid,oldIntercept,cut]']
    else:
        k=9-j if j<9 else j-10
        lines += ['  · norm_num only [grid,oldIntercept,cut,leftAngle,rightAngle,alpha,',
                  '      Nat.cast_ofNat,Int.cast_ofNat,Int.cast_add,Int.cast_mul,',
                  '      Nat.reduceLT,Nat.reduceSub,Int.reduceLT,Int.reduceAdd,Int.reduceMul,',
                  '      Int.reduceSub,Int.reduceNeg,Int.reduceEq,ite_true,ite_false]',
                  f'    rw [value_eq_tan {k} (by norm_num)]']
        if j<9: lines += ['    rw [←tan_neg]']
        lines += ['    congr 1 <;> norm_num <;> ring']
lines += ['','/-- No slope assignment realizes these ten orientation constraints on the','actual BBL grid, regardless of epsilon or of the sizes of the slopes. -/','theorem actual_grid_infeasible (ε : ℝ) :','    ¬ ∃ v : Fin 20→ℝ, ∀ i : Fin 10,','      0<∑ j : Fin 20, coefficient (oldIntercept 5 ε) i j*v j := by','  have he : coefficient (oldIntercept 5 ε)=coefficient (grid (tan (π/20)) ε) := by','    funext i j','    fin_cases i <;> simp only [coefficient,support,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_fin_one]','      <;> rw [grid_eq_actual ε _ (by norm_num),grid_eq_actual ε _ (by norm_num),','        grid_eq_actual ε _ (by norm_num)]','  rw [he]','  exact polynomial_grid_infeasible _ ε tan_quartic tan_root_interval.1 tan_root_interval.2','','#print axioms actual_grid_infeasible','end Kobon.BBLGridObstruction','']
at=lines.index('#print axioms actual_grid_infeasible')
lines[at:at]=['noncomputable def reciprocalLine (a v : Nat→ℝ) (i : Nat) : Line ℝ :=',
  '  ⟨1,-v i,a i⟩','','theorem coefficient_evaluation (a v : Nat→ℝ) (i : Fin 10) :',
  '    (∑ j : Fin 20, coefficient a i j*v j.val)=',
  '      sign i*evalVertex (reciprocalLine a v (support i).k)',
  '        (reciprocalLine a v (support i).i) (reciprocalLine a v (support i).j) := by',
  '  fin_cases i <;> norm_num [Fin.sum_univ_succ,coefficient,sign,support,',
  '    reciprocalLine,evalVertex,vertex,det] <;> ring','',
  '/-- Geometric form: the specified ten determinant signs cannot occur among',
  'real lines x-v_i*y=a_i on the actual tangent grid. -/',
  'theorem actual_grid_orientation_impossible (ε : ℝ) :',
  '    ¬ ∃ v : Nat→ℝ, ∀ i : Fin 10,',
  '      0<sign i*evalVertex (reciprocalLine (oldIntercept 5 ε) v (support i).k)',
  '        (reciprocalLine (oldIntercept 5 ε) v (support i).i)',
  '        (reciprocalLine (oldIntercept 5 ε) v (support i).j) := by',
  '  rintro ⟨v,hv⟩',
  '  apply actual_grid_infeasible ε',
  '  refine ⟨fun j => v j.val,?_⟩',
  '  intro i',
  '  rw [coefficient_evaluation]',
  '  exact hv i','',
  '#print axioms actual_grid_orientation_impossible']
(ROOT/'Kobon/BBLGridObstruction.lean').write_text('\n'.join(lines),encoding='utf-8')
