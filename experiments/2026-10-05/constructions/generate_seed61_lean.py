"""Reproduce exact61-line inputs from the retained rational certificate.

Only immutable input modules are generated. Proof modules are hand-maintained
and compiled separately. Default output is a review directory; --write updates
the repository input modules and requires replay of every dependent proof.
"""
from pathlib import Path
from fractions import Fraction as F
import json,argparse
ROOT=Path(__file__).resolve().parents[3]
parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true');parser.add_argument('--out',type=Path)
args=parser.parse_args()
out=ROOT/'Kobon' if args.write else (args.out or ROOT/'work/seed61-regenerated')
out.mkdir(parents=True,exist_ok=True)
r=json.loads((ROOT/'research/openmath-seven-hour-2026-10-05/constructions/contestant61-refitted-uniform-box.json').read_text())
slopes=list(map(F,r['slopes']));D=10**20
assert len(slopes)==61 and len(r['triangles'])==1190 and len(r['visible'])==28
lo=[int(F(x)*D) for x in r['lo']];hi=[int(F(x)*D) for x in r['hi']]
assert all(F(v,D)==F(x) for v,x in zip(lo,r['lo']))
assert all(F(v,D)==F(x) for v,x in zip(hi,r['hi']))
arr=lambda xs:'#['+','.join(map(str,xs))+']'
def rat(x):
    x=F(x);return str(x.numerator) if x.denominator==1 else f'({x.numerator}/{x.denominator})'
vec=lambda xs:'!['+','.join(map(rat,xs))+']'
ts=lambda xs:'['+','.join('⟨'+','.join(map(str,t))+'⟩' for t in xs)+']'
raw='''import Kobon.OpenMathIntegerBoxes
namespace Kobon.OpenMathConstructionSeed61Fast
open Parametric OpenMathIntegerBoxes
set_option maxRecDepth 100000
set_option maxHeartbeats 0
'''
raw+=f'def gridDen : ℤ := {D}\ndef loInts : Array ℤ := {arr(lo)}\ndef hiInts : Array ℤ := {arr(hi)}\ndef loInt : IntForm 30 := fun i => loInts[i.val]!\ndef hiInt : IntForm 30 := fun i => hiInts[i.val]!\n'
rows=['⟨0,-1,fun _ => 0⟩']
for i in range(1,61):
    k,sign=r['labels'][i];m=slopes[i]
    rows.append(f'⟨{m.numerator},-{m.denominator},fun j => if j.val={k} then {sign*m.numerator} else 0⟩')
raw+='def intLines : Array (IntLine 30) := #[\n  '+',\n  '.join(rows)+']\ndef intLineAt (i : Nat) : IntLine 30 := intLines[i]!\n'
raw+='''def lineFactor (i : Nat) : ℚ := max 1 (-(intLineAt i).b : ℚ)
theorem lineFactor_pos (i : Nat) : 0<lineFactor i :=
  lt_of_lt_of_le (by norm_num : (0 : ℚ)<1) (le_max_left _ _)
end Kobon.OpenMathConstructionSeed61Fast
'''
forms=[(F(0),)*30]+[tuple(slopes[i]*lab[1] if k==lab[0] else F(0) for k in range(30)) for i,lab in enumerate(r['labels'][1:],1)]
data='''import Kobon.OpenMathConstructionSeed61IntegerFastRaw
import Kobon.OpenMathConstructionRescale
import Kobon.HybridBoundary
import Kobon.BBLExtrema
import Kobon.BBLTangent60Bounds
import Mathlib.Tactic.FinCases
/-! Compatible61-line inputs derived from Rohith Poola's61:1190 type.
The rational vector was independently refitted and certified over an entire
actual tangent-grid epsilon box. Counts are certified by separate proof files.
The historical rational array is retained for comparison; the active lines
are defined by exact positive rescaling of independent integer inputs. -/
namespace Kobon.OpenMathConstructionSeed61
open Parametric Exterior HybridBoundary BBLExtrema Real
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def lo : Form 30 := OpenMathIntegerBoxes.grid OpenMathConstructionSeed61Fast.gridDen OpenMathConstructionSeed61Fast.loInt
def hi : Form 30 := OpenMathIntegerBoxes.grid OpenMathConstructionSeed61Fast.gridDen OpenMathConstructionSeed61Fast.hiInt
'''
data+='def lines : Array (ParamLine 30) := #[\n  '+',\n  '.join('⟨'+rat(m)+',-1,'+vec(c)+'⟩' for m,c in zip(slopes,forms))+']\n'
data+='''def lineAt (i : Nat) : ParamLine 30 := OpenMathConstructionRescale.rescale
  (1/OpenMathConstructionSeed61Fast.lineFactor i)
  (OpenMathIntegerBoxes.castLine (OpenMathConstructionSeed61Fast.intLineAt i))
'''
data+='def triangles : List Triple := '+ts(r['triangles'])+'\n'
data+='def distinguished : List Triple := List.ofFn (fun j : Fin 59 => (⟨0,j.val+1,j.val+2⟩ : Triple))\n'
data+='def visible : List Triple := '+ts(r['visible'])+'\n'
data+='def rightSlope : ℚ := '+rat(slopes[-1])+'\nend Kobon.OpenMathConstructionSeed61\n'
for name,content in [('OpenMathConstructionSeed61IntegerFastRaw.lean',raw),('OpenMathConstructionSeed61Data.lean',data)]:
    (out/name).write_text(content,encoding='utf-8',newline='\n')
print(json.dumps(dict(output=str(out),n=61,T=1190,V=28,epsilon=r['epsilon_max'],status='Exact input export; proof replay required'),indent=2))
