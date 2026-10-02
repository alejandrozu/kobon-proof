"""Generate Lean-checked dyadic tangent bounds; Python only proposes bounds."""
from pathlib import Path
from fractions import Fraction as F
import json
import sys

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT / 'research/kobon-hybrid'))
import verify_seed as vs

vs.SCALE = 10**180
vs.PI = 16*vs.atan_inverse(5,180)-4*vs.atan_inverse(239,80)

def rat(v):
    v=F(v)
    return str(v.numerator) if v.denominator==1 else f'({v.numerator}:ℝ)/{v.denominator}'

def bounds(k,q,digits):
    a=vs.tan_pi(k,q);scale=10**digits
    lo=F(a.lo.numerator*scale//a.lo.denominator-2,scale)
    hi=F(-((-a.hi.numerator*scale)//a.hi.denominator)+2,scale)
    return lo,hi

def main():
    body='''import Kobon.BBLTangentBounds

/-! Sharp rational bounds for the tangent grids through denominator48.
Every bound is proved from half-angle and inverse identities in Lean.
The generating Python program is outside the theorem's trust boundary. -/
namespace Kobon.BBLTangent48Bounds
open Real BBLTangentBounds
set_option maxHeartbeats 0

'''
    lo,hi=bounds(1,3,80)
    assert lo*lo<3<hi*hi
    body+=f'''theorem tan_3_1_bounds : {rat(lo)} ≤ tan (1*π/3) ∧ tan (1*π/3) ≤ {rat(hi)} := by
  have heq : 1*π/3=π/3 := by ring
  rw [heq,tan_pi_div_three]
  have hs : (√(3:ℝ))^2=3 := Real.sq_sqrt (by norm_num)
  have hn := Real.sqrt_nonneg (3:ℝ)
  constructor <;> nlinarith

'''
    data={(3,1):(lo,hi)}
    for q in (6,12,24,48):
        # Even indices inherit sharper lower-denominator bounds. At each new
        # half-angle/inverse step we deliberately leave generous error slack.
        order=list(range(2,q//2,2))+[k for k in range(1,q//2,2) if 4*k<q]+([q//4] if q%4==0 else [])+[k for k in range(1,q//2,2) if 4*k>q]
        order=list(dict.fromkeys(order))
        for k in order:
            name=f'tan_{q}_{k}_bounds'
            if 4*k==q:
                lo=hi=F(1)
                proof=f'''  have heq : {k}*π/{q}=π/4 := by ring
  rw [heq,tan_pi_div_four]
  norm_num
'''
            elif k%2==0:
                lo,hi=data[q//2,k//2]
                proof=f'''  have heq : {k}*π/{q}={k//2}*π/{q//2} := by ring
  rw [heq]
  exact tan_{q//2}_{k//2}_bounds
'''
            elif 4*k<q:
                digits={6:70,12:60,24:50,48:40}[q]
                lo,hi=bounds(k,q,digits)
                alo,ahi=data[q//2,k]
                assert 2*lo<=alo*(1-lo*lo)
                assert ahi*(1-hi*hi)<=2*hi
                proof=f'''  obtain ⟨hp,hu⟩ := tan_small ({k}*π/{q}) (by linarith [pi_pos]) (by linarith [pi_pos])
  have hid := tan_half_identity ({k}*π/{q}) (by linarith [pi_pos]) (by linarith [pi_pos])
  have heq : 2*({k}*π/{q})={k}*π/{q//2} := by ring
  rw [heq] at hid
  obtain ⟨hAl,hAu⟩ := tan_{q//2}_{k}_bounds
  exact half_bounds _ _ _ _ ({rat(alo)}) ({rat(ahi)}) hp hu
    (by linarith) hAl hAu (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hid (by norm_num) (by norm_num)
'''
            else:
                digits={6:66,12:56,24:46,48:36}[q]
                lo,hi=bounds(k,q,digits)
                alo,ahi=data[q,q//2-k]
                assert lo*ahi<=1 and hi*alo>=1
                proof=f'''  have heq : {k}*π/{q}=π/2-{q//2-k}*π/{q} := by ring
  rw [heq,tan_pi_div_two_sub]
  obtain ⟨hl,hu⟩ := tan_{q}_{q//2-k}_bounds
  have hp : 0<tan ({q//2-k}*π/{q}) := by linarith
  apply inverse_bounds _ _ _ hp (by norm_num) (by norm_num)
  · nlinarith
  · nlinarith
'''
            data[q,k]=(lo,hi)
            body+=f'theorem {name} : {rat(lo)} ≤ tan ({k}*π/{q}) ∧ tan ({k}*π/{q}) ≤ {rat(hi)} := by\n'+proof+'\n'
    body+='#print axioms tan_48_1_bounds\n#print axioms tan_48_23_bounds\nend Kobon.BBLTangent48Bounds\n'
    (ROOT/'Kobon/BBLTangent48Bounds.lean').write_text(body,encoding='utf-8',newline='\n')
    path=ROOT/'research/three-hour-2026-10-02/bbl/tangent48-bounds.json'
    path.parent.mkdir(parents=True,exist_ok=True)
    path.write_text(json.dumps({str(q):{str(k):[str(v) for v in data[q,k]] for k in range(1,q//2)} for q in (6,12,24,48)},indent=2)+'\n')
    print('Generated exact tangent proposals through q=48.')

if __name__=='__main__': main()
