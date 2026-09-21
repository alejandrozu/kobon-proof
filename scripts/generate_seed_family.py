"""Reproduce the rational box data for the real eleven-line seed theorem.

The Python checks are independent diagnostics. Lean checks the resulting data
and proves the real-parameter conclusion without trusting this generator.
"""
from fractions import Fraction as F
from pathlib import Path
import itertools
import json

ROOT = Path(__file__).resolve().parents[1]
lo = list(map(F, ['3249/10000','7265/10000','13762/10000','30769/10000','0']))
hi = list(map(F, ['3250/10000','7266/10000','13765/10000','30779/10000','1/100000']))
slopes = [F(v,10) for v in [15,-2,14,1,4,-4,5,-3,12,-5]]
forms = []
for k,sign in [(3,-1),(2,-1),(1,-1),(0,-1),(4,-1),(4,1),(0,1),(1,1),(2,1),(3,1)]:
    forms.append([F(sign if j == k else 0) for j in range(5)])
lines = [(F(0),F(1),[F(0)]*5)] + [(F(1),-v,c) for v,c in zip(slopes,forms)]
triangles = sorted(json.loads((ROOT/'research/kobon-hybrid/seed-combinatorics.json').read_text())['triangles'])

def det(l,m): return l[0]*m[1]-l[1]*m[0]
def ev(r,l,m):
    return [r[0]*(m[1]*l[2][i]-l[1]*m[2][i]) +
            r[1]*(l[0]*m[2][i]-m[0]*l[2][i])-det(l,m)*r[2][i] for i in range(5)]
def lower(f): return sum(c*(lo[i] if c >= 0 else hi[i]) for i,c in enumerate(f))
def upper(f): return sum(c*(hi[i] if c >= 0 else lo[i]) for i,c in enumerate(f))
def oriented(r,l,m): return [det(l,m)*v for v in ev(r,l,m)]
for i,j in itertools.combinations(range(11),2): assert det(lines[i],lines[j])
for i,j,k in itertools.combinations(range(11),3):
    f=ev(lines[k],lines[i],lines[j])
    assert lower(f)>0 or upper(f)<0 or (all(f[t]==0 for t in range(4)) and f[4]), (i,j,k)
for i,j,k in triangles:
    for r in lines:
        fs=[oriented(r,lines[a],lines[b]) for a,b in [(i,j),(i,k),(j,k)]]
        assert all(lower(f)>=0 for f in fs) or all(upper(f)<=0 for f in fs), (i,j,k,r)

def q(v):
    v=F(v)
    return str(v.numerator) if v.denominator==1 else f'({v.numerator}/{v.denominator})'
def vector(vs): return '!['+','.join(map(q,vs))+']'
body='''import Kobon.Parametric
import Kobon.TangentBounds
import Mathlib.Tactic.FinCases

/-! A whole family of REAL trigonometric seeds, with arbitrarily small positive
exceptional intercepts. The finite rational box checks below use kernel reduction.
The BBL geometric doubling step is not a theorem of this file. -/
namespace Kobon.SeedFamily
open Parametric Real
set_option maxRecDepth 100000
set_option maxHeartbeats 0

'''
body+=f'def lo : Form 5 := {vector(lo)}\ndef hi : Form 5 := {vector(hi)}\n\n'
body+='def lines : Array (ParamLine 5) := #[\n  '+',\n  '.join('⟨'+q(a)+','+q(b)+','+vector(c)+'⟩' for a,b,c in lines)+']\n\n'
body+='def lineAt (i : Nat) : ParamLine 5 := lines[i]!\n\n'
body+='def triangles : List Triple := [\n  '+',\n  '.join('⟨'+','.join(map(str,t))+'⟩' for t in triangles)+']\n\n'
body+='''theorem directions : DirectionCheck 11 lineAt := by decide +kernel
theorem simple : SimpleCheck 11 lo hi 4 lineAt := by decide +kernel
theorem triangle_checks :
    triangles.all (fun t => decide (TriangleCheck 11 lo hi lineAt t)) = true := by
  decide +kernel
theorem ordered : Increasing 11 triangles := by decide +kernel
theorem distinguished_checks :
    ∀ i : Fin 9, TriangleCheck 11 lo hi lineAt ⟨0,i.val+1,i.val+2⟩ := by
  decide +kernel

noncomputable def parameters (epsilon : ℝ) : Fin 5 → ℝ :=
  ![tan (π/10),tan (π/5),tan (3*π/10),tan (2*π/5),epsilon]

noncomputable def arrangement (epsilon : ℝ) (i : Nat) : Line ℝ :=
  toLine (lineAt i) (parameters epsilon)

theorem parameters_in_box (epsilon : ℝ) (he : 0 < epsilon)
    (hu : epsilon ≤ 1/100000) : InBox lo hi (parameters epsilon) := by
  intro i
  fin_cases i
  · convert TangentBounds.tan_tenth_bounds using 1 <;> norm_num [lo,hi,parameters]
  · convert TangentBounds.tan_fifth_bounds using 1 <;> norm_num [lo,hi,parameters]
  · convert TangentBounds.tan_three_tenths_bounds using 1 <;> norm_num [lo,hi,parameters]
  · convert TangentBounds.tan_two_fifths_bounds using 1 <;> norm_num [lo,hi,parameters]
  · simpa [lo,hi,parameters] using And.intro (le_of_lt he) hu

theorem no_parallel (epsilon : ℝ) : NoParallel 11 (arrangement epsilon) :=
  directions_sound 11 lineAt (parameters epsilon) directions

theorem no_concurrent (epsilon : ℝ) (he : 0 < epsilon)
    (hu : epsilon ≤ 1/100000) : NoConcurrent 11 (arrangement epsilon) := by
  exact simple_sound 11 lo hi 4 lineAt (parameters epsilon)
    (parameters_in_box epsilon he hu) (by simpa [parameters] using he) simple

theorem all_triangles (epsilon : ℝ) (he : 0 < epsilon)
    (hu : epsilon ≤ 1/100000) (t : Triple) (ht : t ∈ triangles) :
    TrianglePredicate 11 (arrangement epsilon) t := by
  have hc := triangle_checks
  simp only [List.all_eq_true,decide_eq_true_eq] at hc
  exact triangle_sound 11 lo hi 4 lineAt (parameters epsilon)
    (parameters_in_box epsilon he hu) (by simpa [parameters] using he) simple t (hc t ht)

/-- Every one of the nine consecutive triples along Y0 is a certified triangle. -/
theorem distinguished_triangles (epsilon : ℝ) (he : 0 < epsilon)
    (hu : epsilon ≤ 1/100000) (i : Fin 9) :
    TrianglePredicate 11 (arrangement epsilon) ⟨0,i.val+1,i.val+2⟩ := by
  exact triangle_sound 11 lo hi 4 lineAt (parameters epsilon)
    (parameters_in_box epsilon he hu) (by simpa [parameters] using he) simple _
    (distinguished_checks i)

theorem simple_lower_bound (epsilon : ℝ) (he : 0 < epsilon)
    (hu : epsilon ≤ 1/100000) : SimpleLowerBound 11 32 := by
  exact ⟨arrangement epsilon,no_parallel epsilon,no_concurrent epsilon he hu,
    triangles,increasing_nodup 11 triangles ordered,all_triangles epsilon he hu,by decide⟩

/-- Exceptional intercepts may be chosen below any positive target tolerance. -/
theorem arbitrarily_small (eta : ℝ) (heta : 0 < eta) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ epsilon < eta ∧ epsilon ≤ 1/100000 ∧
      NoParallel 11 (arrangement epsilon) ∧ NoConcurrent 11 (arrangement epsilon) ∧
      (∀ t ∈ triangles, TrianglePredicate 11 (arrangement epsilon) t) ∧
      (∀ i : Fin 9, TrianglePredicate 11 (arrangement epsilon) ⟨0,i.val+1,i.val+2⟩) := by
  let epsilon := min ((1:ℝ)/100000) (eta/2)
  have he : 0 < epsilon := lt_min (by norm_num) (by linarith)
  have hu : epsilon ≤ 1/100000 := min_le_left _ _
  have het : epsilon < eta := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  exact ⟨epsilon,he,het,hu,no_parallel epsilon,no_concurrent epsilon he hu,
    all_triangles epsilon he hu,distinguished_triangles epsilon he hu⟩

#print axioms arbitrarily_small
#print axioms simple_lower_bound
end Kobon.SeedFamily
'''
(ROOT/'Kobon/SeedFamily.lean').write_text(body,encoding='utf-8',newline='\n')
print('Exact rational box checks passed; wrote Kobon/SeedFamily.lean.')
