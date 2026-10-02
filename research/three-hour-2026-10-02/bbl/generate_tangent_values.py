"""Emit the small exact algebra bridge; generated Lean is independently checked."""
from pathlib import Path
import json,sys
ROOT=Path(__file__).resolve().parents[3]
sys.path.insert(0,str(ROOT/'work/python-deps'))
import sympy as s
t=s.symbols('t')
data=json.loads((ROOT/'research/three-hour-2026-10-02/constructions/grid21-obstruction/representative-238.json').read_text(encoding='utf-8'))
def poly(cs):return sum(s.Rational(c)*t**j for j,c in enumerate(reversed(cs)))
def lean(z):return str(s.expand(z)).replace('**','^')
p=[poly(data['tangent_coefficients'][str(k)]) for k in range(10)]
Q=t**4-4*t**3-14*t**2-4*t+1
lines=['import Kobon.BBLTangentAlgebra','import Mathlib.Tactic.IntervalCases','','/-! Exact power-basis expressions for every noncentral intercept in the','20-line tangent grid. Every polynomial identity is kernel checked. -/','namespace Kobon.BBLTangentValues','open Real BBLTangentAlgebra BBLGrid','set_option maxHeartbeats 0','','noncomputable def value : Nat → ℝ → ℝ']
lines += [f'  | {k}, t => {lean(v)}' for k,v in enumerate(p)]
lines += ['  | _, _ => 0','','theorem value_step (t : ℝ) (hq : quartic t=0) (k : Nat) (hk : k<9) :','    value (k+1) t*(1-value k t*t)=value k t+t := by','  interval_cases k']
for k in range(9):
    a,b=s.div(s.expand(p[k+1]*(1-p[k]*t)-p[k]-t),Q,t)
    assert b==0
    lines += ['  · norm_num only [value]','    unfold quartic at hq',f'    linear_combination ({lean(a)})*hq']
lines += ['','theorem multiple_cos_pos (k : Nat) (hk : k<10) :','    0<cos ((k:ℝ)*(π/20)) := by','  have hkn : (0:ℝ)≤k := Nat.cast_nonneg k','  have hku : (k:ℝ)<10 := by exact_mod_cast hk','  apply cos_pos_of_mem_Ioo','  constructor <;> nlinarith [pi_pos,mul_nonneg hkn (le_of_lt pi_pos),','    mul_pos (sub_pos.mpr hku) pi_pos]','','theorem value_eq_tan (k : Nat) (hk : k<10) :','    value k (tan (π/20))=tan ((k:ℝ)*(π/20)) := by','  induction k with','  | zero => simp [value]','  | succ k ih =>','    have hk9 : k<9 := by omega','    have ih := ih (by omega)','    have hc0 : cos (π/20)≠0 := ne_of_gt (by simpa using multiple_cos_pos 1 (by norm_num))','    have hck : cos ((k:ℝ)*(π/20))≠0 := ne_of_gt (multiple_cos_pos k (by omega))','    have hcs : cos ((k:ℝ)*(π/20)+π/20)≠0 := by','      have he : (k:ℝ)*(π/20)+π/20=((k+1:Nat):ℝ)*(π/20) := by push_cast; ring','      rw [he]','      exact ne_of_gt (multiple_cos_pos (k+1) hk)','    have hd : 1-tan ((k:ℝ)*(π/20))*tan (π/20)≠0 := by','      intro hh','      have hp := tangent_product_identity ((k:ℝ)*(π/20)) (π/20) hck hc0','      rw [hh,zero_mul] at hp','      exact hcs hp.symm','    have hs := value_step (tan (π/20)) tan_quartic k hk9','    rw [ih] at hs','    have hh := tangent_sum_rational ((k:ℝ)*(π/20)) (π/20) hck hc0 hcs','    have he : ((k+1:Nat):ℝ)*(π/20)=(k:ℝ)*(π/20)+π/20 := by push_cast; ring','    rw [he,←hh]','    exact (eq_div_iff hd).mpr hs','','#print axioms value_eq_tan','end Kobon.BBLTangentValues','']
(ROOT/'Kobon/BBLTangentValues.lean').write_text('\n'.join(lines),encoding='utf-8')
