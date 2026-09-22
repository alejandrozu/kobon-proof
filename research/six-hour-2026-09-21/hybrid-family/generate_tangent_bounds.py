"""Generate exact Lean enclosures at multiples of pi/20.

Python proposes rational endpoints. Lean derives their validity from algebraic
trigonometric identities; this generator is not a trusted numeric oracle.
"""
from pathlib import Path
import sys
import math

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0,str(ROOT/'research/kobon-hybrid'))
from verify_seed import tan_pi, F

S=10**30
scales={k:10**p for k,p in {1:30,2:40,3:30,4:40,5:30,6:35,7:25,8:35,9:25}.items()}
RS=10**50
r=math.isqrt(5*RS*RS)
values={k:tan_pi(k,20) for k in range(1,10)}
bounds={k:(v.lo.numerator*scales[k]//v.lo.denominator,
           v.hi.numerator*scales[k]//v.hi.denominator+1) for k,v in values.items()}
bounds[5]=(S,S)

def val(k,side):
    return f'({bounds[k][side]}:ℝ)/{scales[k]}'

def statement(k):
    return f'{val(k,0)} ≤ tan ({k}*π/20) ∧ tan ({k}*π/20) ≤ {val(k,1)}'

lines=['''import Kobon.TangentBounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

/-! Sharp rational enclosures for the actual nine positive tangent-grid values.
All inequalities are checked from trigonometric identities in Lean.
-/
namespace Kobon.BBLTangentBounds
open Real
set_option maxHeartbeats 0

theorem inverse_bounds (x L U : ℝ) (hx : 0<x) (hL : 0≤L) (hU : 0≤U)
    (hl : L*x≤1) (hu : 1≤U*x) : L≤x⁻¹ ∧ x⁻¹≤U := by
  have hi := mul_inv_cancel₀ (ne_of_gt hx)
  constructor
  · by_contra h
    have hmul := mul_pos (sub_pos.mpr (lt_of_not_ge h)) hx
    nlinarith
  · by_contra h
    have hmul := mul_pos (sub_pos.mpr (lt_of_not_ge h)) hx
    nlinarith

theorem half_bounds (t A L U Alo Ahi : ℝ) (ht : 0<t) (ht1 : t<1)
    (hA : 0<A) (hAl : Alo≤A) (hAu : A≤Ahi)
    (hL : 0≤L) (hL1 : L<1) (hU : 0≤U) (hU1 : U<1)
    (hid : A*(1-t^2)=2*t)
    (hl : 2*L≤Alo*(1-L^2)) (hu : Ahi*(1-U^2)≤2*U) : L≤t ∧ t≤U := by
  have hls : 0≤1-L^2 := by nlinarith
  have hus : 0≤1-U^2 := by nlinarith
  have hlow : 2*L≤A*(1-L^2) := le_trans hl (mul_le_mul_of_nonneg_right hAl hls)
  have hupp : A*(1-U^2)≤2*U := le_trans (mul_le_mul_of_nonneg_right hAu hus) hu
  constructor
  · by_contra h
    have htl : t<L := lt_of_not_ge h
    have hs : 0<L^2-t^2 := by nlinarith
    have hm := mul_pos hA hs
    nlinarith
  · by_contra h
    have hut : U<t := lt_of_not_ge h
    have hs : 0<t^2-U^2 := by nlinarith
    have hm := mul_pos hA hs
    nlinarith

theorem tan_small (x : ℝ) (hx : 0<x) (hx4 : x<π/4) :
    0<tan x ∧ tan x<1 := by
  constructor
  · exact tan_pos_of_pos_of_lt_pi_div_two hx (by linarith [pi_pos])
  · rw [← tan_pi_div_four]
    apply strictMonoOn_tan
    · constructor <;> linarith [pi_pos]
    · constructor <;> linarith [pi_pos]
    · exact hx4

theorem tan_half_identity (x : ℝ) (hx : 0<x) (hx4 : x<π/4) :
    tan (2*x)*(1-(tan x)^2)=2*tan x := by
  obtain ⟨hp,hu⟩ := tan_small x hx hx4
  have hn : 1-(tan x)^2 ≠ 0 := by nlinarith
  rw [tan_two_mul]
  exact div_mul_cancel₀ _ hn
''']
lines.append(f'''theorem sqrt_five_sharp : ({r}:ℝ)/{RS} ≤ √5 ∧ √5 ≤ {r+1}/{RS} := by
  have hs : (√(5:ℝ))^2=5 := Real.sq_sqrt (by norm_num)
  have hn := Real.sqrt_nonneg (5:ℝ)
  constructor <;> nlinarith
''')
for k,coeff,rhs,theorem,arg in [(2,5,3,'tan_tenth_identity','π/10'),(4,3,5,'tan_fifth_identity','π/5')]:
    lines.append(f'''theorem tan_{k}_bounds : {statement(k)} := by
  have heq : {k}*π/20={arg} := by ring
  rw [heq]
  have hp : 0 < tan ({arg}) := tan_pos_of_pos_of_lt_pi_div_two (by linarith [pi_pos]) (by linarith [pi_pos])
  have ha : 0 < {coeff}+√(5:ℝ) := by positivity
  have h := TangentBounds.{theorem}
  obtain ⟨hl,hu⟩ := sqrt_five_sharp
  have hlow : ({val(k,0)})^2 ≤ (tan ({arg}))^2 := by
    apply (mul_le_mul_iff_right₀ ha).mp
    rw [h]
    nlinarith
  have hhigh : (tan ({arg}))^2 ≤ ({val(k,1)})^2 := by
    apply (mul_le_mul_iff_right₀ ha).mp
    rw [h]
    nlinarith
  constructor <;> nlinarith
''')
for k,base in [(6,4),(8,2)]:
    lines.append(f'''theorem tan_{k}_bounds : {statement(k)} := by
  have heq : {k}*π/20=π/2-{base}*π/20 := by ring
  rw [heq,tan_pi_div_two_sub]
  obtain ⟨hl,hu⟩ := tan_{base}_bounds
  have hp : 0<tan ({base}*π/20) := by linarith
  apply inverse_bounds _ _ _ hp (by norm_num) (by norm_num)
  · nlinarith
  · nlinarith
''')
for k,base in [(1,2),(3,6)]:
    lines.append(f'''theorem tan_{k}_bounds : {statement(k)} := by
  obtain ⟨hp,hu⟩ := tan_small ({k}*π/20) (by linarith [pi_pos]) (by linarith [pi_pos])
  have hid := tan_half_identity ({k}*π/20) (by linarith [pi_pos]) (by linarith [pi_pos])
  have heq : 2*({k}*π/20)={base}*π/20 := by ring
  rw [heq] at hid
  obtain ⟨hAl,hAu⟩ := tan_{base}_bounds
  exact half_bounds _ _ _ _ ({val(base,0)}) ({val(base,1)}) hp hu
    (by linarith) hAl hAu (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hid (by norm_num) (by norm_num)
''')
lines.append(f'''theorem tan_5_bounds : {statement(5)} := by
  have heq : 5*π/20=π/4 := by ring
  rw [heq,tan_pi_div_four]
  norm_num
''')
for k,base in [(7,3),(9,1)]:
    lines.append(f'''theorem tan_{k}_bounds : {statement(k)} := by
  have heq : {k}*π/20=π/2-{base}*π/20 := by ring
  rw [heq,tan_pi_div_two_sub]
  obtain ⟨hl,hu⟩ := tan_{base}_bounds
  have hp : 0<tan ({base}*π/20) := by linarith
  apply inverse_bounds _ _ _ hp (by norm_num) (by norm_num)
  · nlinarith
  · nlinarith
''')
lines.append('''#print axioms tan_1_bounds
#print axioms tan_9_bounds
end Kobon.BBLTangentBounds
''')
(ROOT/'Kobon/BBLTangentBounds.lean').write_text('\n'.join(lines),encoding='utf-8')
