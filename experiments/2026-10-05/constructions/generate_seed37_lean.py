from pathlib import Path
from fractions import Fraction as F
import json,re,argparse,sys
R=Path(__file__).resolve().parents[3];parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true');parser.add_argument('--out',type=Path);args=parser.parse_args();out=R/'Kobon' if args.write else (args.out or R/'work/seed37-regenerated');out.mkdir(parents=True,exist_ok=True);r=json.loads((R/'research/openmath-seven-hour-2026-10-05/constructions/contestant37-uniform-box.json').read_text());N=37;d=18;D=10**20;prefix='OpenMathConstructionSeed37';ms=list(map(F,r['slopes']))
arr=lambda xs:'#['+','.join(map(str,xs))+']'
def rat(x):
 x=F(x);return str(x.numerator) if x.denominator==1 else f'({x.numerator}/{x.denominator})'
vec=lambda xs:'!['+','.join(map(rat,xs))+']'
ts=lambda xs:'['+','.join('⟨'+','.join(map(str,t))+'⟩' for t in xs)+']'
lo=[int(F(x)*D) for x in r['lo']];hi=[int(F(x)*D) for x in r['hi']]
raw=f'''import Kobon.OpenMathIntegerBoxes
namespace Kobon.{prefix}Fast
open Parametric OpenMathIntegerBoxes
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def gridDen : ℤ := {D}
def loInts : Array ℤ := {arr(lo)}
def hiInts : Array ℤ := {arr(hi)}
def loInt : IntForm {d} := fun i => loInts[i.val]!
def hiInt : IntForm {d} := fun i => hiInts[i.val]!
'''
rows=['⟨0,-1,fun _ => 0⟩']
for i in range(1,N):
 k,sg=r['labels'][i];m=ms[i];rows.append(f'⟨{m.numerator},-{m.denominator},fun j => if j.val={k} then {sg*m.numerator} else 0⟩')
raw+=f'def intLines : Array (IntLine {d}) := #[\n  '+',\n  '.join(rows)+']\ndef intLineAt (i : Nat) : IntLine '+str(d)+' := intLines[i]!\n'
raw+='''def lineFactor (i : Nat) : ℚ := max 1 (-(intLineAt i).b : ℚ)
theorem lineFactor_pos (i : Nat) : 0<lineFactor i :=
  lt_of_lt_of_le (by norm_num : (0 : ℚ)<1) (le_max_left _ _)
'''+f'end Kobon.{prefix}Fast\n'
(out/f'{prefix}IntegerFastRaw.lean').write_text(raw)
forms=[(F(0),)*d]+[tuple(ms[i]*lab[1] if k==lab[0] else F(0) for k in range(d)) for i,lab in enumerate(r['labels'][1:],1)]
data=f'''import Kobon.{prefix}IntegerFastRaw
import Kobon.OpenMathConstructionRescale
import Kobon.HybridBoundary
import Kobon.BBLExtrema
import Mathlib.Tactic.FinCases
/-! Independent uniform37/431 fixed-slope certificate inputs. The numerical
q18 family retains its Parpalak--Utkin/Blanc attribution; the input point is
from Rohith Poola's competition source. The actual tangent and geometric
proofs are separate from these rational finite certificate data. -/
namespace Kobon.{prefix}
open Parametric Exterior HybridBoundary BBLExtrema Real
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def lo : Form {d} := OpenMathIntegerBoxes.grid {prefix}Fast.gridDen {prefix}Fast.loInt
def hi : Form {d} := OpenMathIntegerBoxes.grid {prefix}Fast.gridDen {prefix}Fast.hiInt
'''
data+=f'def lines : Array (ParamLine {d}) := #[\n  '+',\n  '.join('⟨'+rat(m)+',-1,'+vec(c)+'⟩' for m,c in zip(ms,forms))+']\n'
data+=f'''def lineAt (i : Nat) : ParamLine {d} := OpenMathConstructionRescale.rescale
  (1/{prefix}Fast.lineFactor i)
  (OpenMathIntegerBoxes.castLine ({prefix}Fast.intLineAt i))
def triangles : List Triple := {ts(r['triangles'])}
def distinguished : List Triple := List.ofFn (fun j : Fin 35 => (⟨0,j.val+1,j.val+2⟩ : Triple))
end Kobon.{prefix}
'''
(out/f'{prefix}Data.lean').write_text(data)
if args.write:
 print('Immutable37 input export; dependent proof replay required');sys.exit(0)
replace={'61':'37','60':'36','59':'35','30':'18','31':'19','29':'17','1190':'431','15':'9'}
def adapt(s):
 s=s.replace('OpenMathConstructionSeed61',prefix)
 return re.sub(r'\b(61|60|59|30|31|29|1190|15)\b',lambda m:replace[m.group(0)],s)
for suffix in['IntegerFastData','IntegerFastSimple','IntegerFastTriangles','Simple','Triangles']:
 s=adapt((R/'Kobon'/('OpenMathConstructionSeed61'+suffix+'.lean')).read_text()).replace('61-integer-fast','37-integer-fast')
 (out/(prefix+suffix+'.lean')).write_text(s)
s=adapt((R/'Kobon/OpenMathConstructionSeed61Checks.lean').read_text());s=s[:s.index('theorem admissible_bool')]+f'''#print axioms simple
#print axioms triangle_checks
end Kobon.{prefix}
''';(out/(prefix+'Checks.lean')).write_text(s)
params=','.join(f'tan ({k}*π/36)' for k in range(1,18))+',epsilon'
base=f'''import Kobon.{prefix}Checks
import Kobon.BBLTangent36Bounds
namespace Kobon.{prefix}
open Parametric Exterior HybridBoundary BBLExtrema Real
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def parameters (epsilon : ℝ) : Fin 18 → ℝ := ![{params}]
noncomputable def arrangement (epsilon : ℝ) (i : Nat) : Line ℝ :=
  toLine (lineAt i) (parameters epsilon)
theorem parameters_in_box (epsilon : ℝ) (he : 0<epsilon) (hu : epsilon≤(1/100000000)) :
    InBox lo hi (parameters epsilon) := by
  intro i
  fin_cases i
'''
for k in range(1,18):
 base+=f'''  · have h := BBLTangent36Bounds.tan_{k}_bounds
    try simp only [one_mul] at h
    norm_num [lo,hi,parameters,OpenMathIntegerBoxes.grid,{prefix}Fast.gridDen,
      {prefix}Fast.loInt,{prefix}Fast.hiInt,{prefix}Fast.loInts,{prefix}Fast.hiInts]
    constructor <;> linarith [h.1,h.2]
'''
base+=f'''  · norm_num [lo,hi,parameters,OpenMathIntegerBoxes.grid,{prefix}Fast.gridDen,
      {prefix}Fast.loInt,{prefix}Fast.hiInt,{prefix}Fast.loInts,{prefix}Fast.hiInts]
    exact ⟨he.le,hu⟩
theorem no_parallel (epsilon : ℝ) : NoParallel 37 (arrangement epsilon) :=
  directions_sound 37 lineAt (parameters epsilon) directions
theorem no_concurrent (epsilon : ℝ) (he : 0<epsilon) (hu : epsilon≤(1/100000000)) :
    NoConcurrent 37 (arrangement epsilon) :=
  simple_sound 37 lo hi 17 lineAt (parameters epsilon) (parameters_in_box epsilon he hu)
    (by simpa [parameters] using he) simple
theorem all_triangles (epsilon : ℝ) (he : 0<epsilon) (hu : epsilon≤(1/100000000))
    (t : Triple) (ht : t∈triangles) : TrianglePredicate 37 (arrangement epsilon) t := by
  exact triangle_sound 37 lo hi 17 lineAt (parameters epsilon) (parameters_in_box epsilon he hu)
    (by simpa [parameters] using he) simple t (of_decide_eq_true ((List.all_eq_true.mp triangle_checks) t ht))
theorem all_distinguished (epsilon : ℝ) (he : 0<epsilon) (hu : epsilon≤(1/100000000))
    (t : Triple) (ht : t∈distinguished) : TrianglePredicate 37 (arrangement epsilon) t := by
  exact triangle_sound 37 lo hi 17 lineAt (parameters epsilon) (parameters_in_box epsilon he hu)
    (by simpa [parameters] using he) simple t (of_decide_eq_true ((List.all_eq_true.mp distinguished_checks) t ht))
theorem simple_lower_bound (epsilon : ℝ) (he : 0<epsilon) (hu : epsilon≤(1/100000000)) :
    SimpleLowerBound 37 431 := by
  exact ⟨arrangement epsilon,no_parallel epsilon,no_concurrent epsilon he hu,triangles,
    increasing_nodup 37 triangles ordered,all_triangles epsilon he hu,by decide⟩
#print axioms simple_lower_bound
end Kobon.{prefix}
''';(out/(prefix+'.lean')).write_text(base)
s=adapt((R/'Kobon/OpenMathConstructionSeed61Normalized.lean').read_text()).replace('20000000000/9239253',r['central_height_coefficient']);(out/(prefix+'Normalized.lean')).write_text(s)
print(json.dumps(dict(n=37,T=431,eta=r['epsilon_max'],central_height=r['central_height_coefficient'],status='Source export; full replay pending')))
