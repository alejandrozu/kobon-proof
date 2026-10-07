from pathlib import Path
import json
from fractions import Fraction as F
R=Path(__file__).resolve().parents[3]
r=json.loads((R/'research/openmath-seven-hour-2026-10-05/constructions/contestant61-refitted-uniform-box.json').read_text())
s=list(map(F,r['slopes']));D=10**20
lo=[int(F(t)*D) for t in r['lo']];hi=[int(F(t)*D) for t in r['hi']]
v=lambda x:'#['+','.join(map(str,x))+']'
a='''import Kobon.OpenMathConstructionSeed61Data
import Kobon.OpenMathIntegerBoxes
namespace Kobon.OpenMathConstructionSeed61Fast
open Parametric OpenMathIntegerBoxes
set_option maxRecDepth 100000
set_option maxHeartbeats 0
'''
a+=f'def gridDen : ℤ := {D}\ndef loInts : Array ℤ := {v(lo)}\ndef hiInts : Array ℤ := {v(hi)}\ndef loInt : IntForm 30 := fun i => loInts[i.val]!\ndef hiInt : IntForm 30 := fun i => hiInts[i.val]!\n'
rows=['⟨0,-1,fun _ => 0⟩']
for i in range(1,61):
    k,sign=r['labels'][i];m=s[i]
    rows.append(f'⟨{m.numerator},-{m.denominator},fun j => if j.val={k} then {sign*m.numerator} else 0⟩')
a+='def intLines : Array (IntLine 30) := #[\n  '+',\n  '.join(rows)+']\ndef intLineAt (i : Nat) : IntLine 30 := intLines[i]!\nend Kobon.OpenMathConstructionSeed61Fast\n'
(R/'Kobon/OpenMathConstructionSeed61IntegerFastRaw.lean').write_text(a,encoding='utf-8',newline='\n')
print('Wrote direct-array bounds and single-index coefficients')
