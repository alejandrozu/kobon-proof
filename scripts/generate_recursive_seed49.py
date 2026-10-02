"""Export the exact, sorted 49-line uniform seed for independent Lean checking.

The input is an exact interval-certified construction, not a Lean theorem.
The generated module uses the existing checked Parametric box semantics and
the separately proved actual tangent enclosures. No floating arithmetic is
used by this exporter. Numerical priority for 49:767 is not claimed.
"""
from fractions import Fraction as F
from pathlib import Path
import json

ROOT=Path(__file__).resolve().parents[1]
DATA=ROOT/'research/three-hour-2026-10-02/constructions/uniform-grid49/uniform-seed.json'
BOUND=ROOT/'research/three-hour-2026-10-02/bbl/tangent48-bounds.json'

def rat(x):
    x=F(x)
    return str(x.numerator) if x.denominator==1 else f'({x.numerator}/{x.denominator})'
def vector(xs):return '!['+','.join(map(rat,xs))+']'
def triples(ts):return '['+','.join('⟨'+','.join(map(str,t))+'⟩' for t in ts)+']'

def main():
    data=json.loads(DATA.read_text())
    bounds=json.loads(BOUND.read_text())['48']
    den=10**30
    lo=[F((F(bounds[str(k)][0])*den).__floor__(),den) for k in range(1,24)]+[F(0)]
    hi=[F((F(bounds[str(k)][1])*den).__ceil__(),den) for k in range(1,24)]+[F(1,100)]
    slopes=[F(0)]+[1/F(v) for v in data['reciprocal_slopes']]
    labels=[None]+[(k-1,-1) for k in range(23,0,-1)]+[(23,-1),(23,1)]+[(k-1,1) for k in range(1,24)]
    assert len(slopes)==len(labels)==49
    body='''import Kobon.BBLTangent48Bounds
import Kobon.ParametricCached
import Kobon.HybridBoundary
import Kobon.BBLExtrema
import Mathlib.Tactic.FinCases

/-! Uniform 49-line parameter certificate. The fixed rational slopes and
actual tan(k*pi/48) intercepts supply a sorted seed. Finite box checks use
native evaluation; all geometric conclusions use proved soundness lemmas. -/
namespace Kobon.BBLSeed49
open Parametric Exterior HybridBoundary BBLExtrema Real
set_option maxRecDepth 100000
set_option maxHeartbeats 0

'''
    body+=f'def lo : Form 24 := {vector(lo)}\ndef hi : Form 24 := {vector(hi)}\n\n'
    entries=[]
    for m,label in zip(slopes,labels):
        coeff=[F(0)]*24
        if label is not None:coeff[label[0]]=label[1]*m
        entries.append('⟨'+rat(m)+',-1,'+vector(coeff)+'⟩')
    body+='def lines : Array (ParamLine 24) := #[\n  '+',\n  '.join(entries)+']\n'
    body+='def lineAt (i : Nat) : ParamLine 24 := lines[i]!\n\n'
    body+='def triangles : List Triple := '+triples(data['triangles'])+'\n'
    body+='def distinguished : List Triple := '+triples([[0,j+1,j+2] for j in range(47)])+'\n\n'
    body+='''theorem directions : DirectionCheck 49 lineAt := by native_decide
#print axioms directions
theorem simple : SimpleCheck 49 lo hi 23 lineAt := by
  have h : ParametricCached.SimpleCheck 49 lo hi 23 lineAt := by native_decide
  exact ParametricCached.simple_sound 49 lo hi 23 lineAt h
#print axioms simple
theorem cached_triangle_checks :
    triangles.all (fun t => decide (ParametricCached.TriangleCheck 49 lo hi lineAt t))=true := by native_decide
#print axioms cached_triangle_checks
theorem triangle_checks :
    triangles.all (fun t => decide (TriangleCheck 49 lo hi lineAt t))=true := by
  simpa only [← ParametricCached.triangle_eq] using cached_triangle_checks
theorem ordered : Increasing 49 triangles := by native_decide
theorem distinguished_subset : ∀ t∈distinguished, t∈triangles := by native_decide

'''
    body+='noncomputable def parameters (epsilon : ℝ) : Fin 24→ℝ := !['+','.join(f'tan ({k}*π/48)' for k in range(1,24))+',epsilon]\n'
    body+='''noncomputable def arrangement (epsilon : ℝ) (i : Nat) : Line ℝ :=
  toLine (lineAt i) (parameters epsilon)

theorem parameters_in_box (epsilon : ℝ) (he : 0<epsilon) (hu : epsilon≤1/100) :
    InBox lo hi (parameters epsilon) := by
  intro i
  fin_cases i
'''
    for k in range(1,24):
        body+=f'  · have h := BBLTangent48Bounds.tan_48_{k}_bounds\n    norm_num [lo,hi,parameters]\n    constructor <;> linarith [h.1,h.2]\n'
    body+='  · simpa [lo,hi,parameters] using And.intro (le_of_lt he) hu\n\n'
    body+='''theorem no_parallel (epsilon : ℝ) : NoParallel 49 (arrangement epsilon) :=
  directions_sound 49 lineAt (parameters epsilon) directions

theorem no_concurrent (epsilon : ℝ) (he : 0<epsilon) (hu : epsilon≤1/100) :
    NoConcurrent 49 (arrangement epsilon) := by
  exact simple_sound 49 lo hi 23 lineAt (parameters epsilon)
    (parameters_in_box epsilon he hu) (by simpa [parameters] using he) simple

theorem all_triangles (epsilon : ℝ) (he : 0<epsilon) (hu : epsilon≤1/100)
    (t : Triple) (ht : t∈triangles) : TrianglePredicate 49 (arrangement epsilon) t := by
  have hc := triangle_checks
  simp only [List.all_eq_true,decide_eq_true_eq] at hc
  exact triangle_sound 49 lo hi 23 lineAt (parameters epsilon)
    (parameters_in_box epsilon he hu) (by simpa [parameters] using he) simple t (hc t ht)

theorem all_distinguished (epsilon : ℝ) (he : 0<epsilon) (hu : epsilon≤1/100)
    (t : Triple) (ht : t∈distinguished) : TrianglePredicate 49 (arrangement epsilon) t :=
  all_triangles epsilon he hu t (distinguished_subset t ht)

theorem simple_lower_bound (epsilon : ℝ) (he : 0<epsilon) (hu : epsilon≤1/100) :
    SimpleLowerBound 49 767 := by
  exact ⟨arrangement epsilon,no_parallel epsilon,no_concurrent epsilon he hu,
    triangles,increasing_nodup 49 triangles ordered,all_triangles epsilon he hu,by decide⟩

#print axioms simple_lower_bound
end Kobon.BBLSeed49
'''
    target=ROOT/'research/three-hour-2026-10-02/drafts/BBLSeed49.lean'
    target.write_text(body,encoding='utf-8',newline='\n')
    print('Wrote draft BBLSeed49.lean; full Lean compilation has not completed.')

if __name__=='__main__':main()
