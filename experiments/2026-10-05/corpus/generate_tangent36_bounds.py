"""Generate kernel-checked quarter-angle certificates for tan(k*pi/36).

Arb only chooses candidate rationals. Exact Fraction checks and Lean's kernel
establish every inequality; the floating library is outside the proof trust.
"""
from pathlib import Path
from fractions import Fraction as F
import json, sys

ROOT=Path(__file__).resolve().parents[3]
sys.path.insert(0,str(ROOT/'work/construction-deps'))
from flint import arb,ctx
ctx.prec=180
BASE=ROOT/'research/openmath-seven-hour-2026-10-05/corpus/tangent36'
BASE.mkdir(parents=True,exist_ok=True)
wide=json.loads((ROOT/'research/openmath-seven-hour-2026-10-05/constructions/tangent36-proposed-wide-bounds.json').read_text())
PI_LO=F(314159265358979323846,10**20)
PI_HI=F(314159265358979323847,10**20)
def poly(n,x):return sum(((-1)**i*x**(2*i+1)/F(2*i+1) for i in range(n)),F(0))
def twice(x):return 2*x/(1-x*x)
def rat(x,typ='ℚ'):return f'(({x.numerator}:{typ})/{x.denominator})'

lines=['import Kobon.BBLRationalTangentBounds','',
 '/-! Actual denominator-36 tangent bounds. Candidate endpoints are generated',
 'externally, but all Taylor remainder conditions are checked in the kernel.',
 'The final endpoints match the exact interval certificate of the 37-line seed. -/',
 'namespace Kobon.BBLTangent36Bounds','open Real BBLRationalTangentBounds',
 'set_option maxHeartbeats 0','set_option maxRecDepth 100000','']
records={}
for k in range(1,18):
    x=F(str((arb.pi()*k/144).tan().mid().fmpq()))
    D=10**22
    mid=x.numerator*D//x.denominator
    lo,hi=F(mid-100,D),F(mid+101,D)
    wlo,whi=map(F,wide[str(k)])
    assert 0<=lo<hi<1 and twice(hi)<1
    assert poly(33,lo)<=k*PI_LO/144
    assert k*PI_HI/144<=poly(32,hi)
    tlo,thi=twice(twice(lo)),twice(twice(hi))
    assert wlo<=tlo<=thi<=whi
    records[str(k)]={'quarter_lo':str(lo),'quarter_hi':str(hi),'lo':str(wlo),'hi':str(whi),'terms':16}
    lines += [f'def quarterLo{k} : ℚ := {rat(lo)}',f'def quarterHi{k} : ℚ := {rat(hi)}',
      f'theorem quarter_check_{k} : QuarterCheck 36 {k} 16 quarterLo{k} quarterHi{k} := by',
      '  decide +kernel','',
      f'theorem tan_{k}_bounds : {rat(wlo,"ℝ")}≤tan ({k}*π/36) ∧',
      f'    tan ({k}*π/36)≤{rat(whi,"ℝ")} := by',
      f'  obtain ⟨hl,hu⟩ := quarterCheck_sound quarter_check_{k}',
      f'  have low : ({rat(wlo)}:ℝ)≤(twiceRat (twiceRat quarterLo{k}):ℝ) := by',
      '    exact_mod_cast (show '+rat(wlo)+f'≤twiceRat (twiceRat quarterLo{k}) by decide +kernel)',
      f'  have high : (twiceRat (twiceRat quarterHi{k}):ℝ)≤({rat(whi)}:ℝ) := by',
      '    exact_mod_cast (show '+f'twiceRat (twiceRat quarterHi{k})≤'+rat(whi)+' by decide +kernel)',
      '  constructor',
      '  · simpa only [angle, Nat.cast_ofNat, Nat.cast_one, Rat.cast_div, Rat.cast_ofNat] using low.trans hl',
      '  · simpa only [angle, Nat.cast_ofNat, Nat.cast_one, Rat.cast_div, Rat.cast_ofNat] using hu.trans high','']
lines+=['#print axioms tan_1_bounds','#print axioms tan_17_bounds','end Kobon.BBLTangent36Bounds','']
(ROOT/'Kobon/BBLTangent36Bounds.lean').write_text('\n'.join(lines),encoding='utf-8')
(BASE/'bounds.json').write_text(json.dumps(records,indent=2)+'\n')
print('Generated 17 exact quarter certificates and matching wide endpoints.')
