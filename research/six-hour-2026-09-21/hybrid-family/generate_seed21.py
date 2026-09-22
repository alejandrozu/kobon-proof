"""A rational-slope, exact-trigonometric 21-line compatible seed.

Coordinates of the reference certificate are rational; the generated Lean
module proves the whole family with true tangent-grid intercepts and an
arbitrarily small positive exceptional intercept.  Native reduction is used
for the finite rational-box checks; soundness is the generic Lean theorem.
"""
from pathlib import Path
import sys,json
from itertools import combinations

ROOT=Path(__file__).resolve().parents[3]
sys.path.insert(0,str(ROOT/'research/kobon-hybrid'))
from verify_seed import F,EPS,V,tan_pi
from exact_geometry import arrangement,primitive
from verify_direct import verify
from generate_tangent_bounds import bounds,scales

def qstr(x):
    x=F(x)
    return str(x.numerator) if x.denominator==1 else f'({x.numerator}/{x.denominator})'

def form(k=None,c=1):
    out=[F(0)]*10
    if k is not None:out[k]=F(c)
    return out

def add(x,y):return [a+b for a,b in zip(x,y)]
def sub(x,y):return [a-b for a,b in zip(x,y)]
def scale(c,x):return [c*a for a in x]
def det(l,m):return l[0]*m[1]-l[1]*m[0]
def evaluate_form(r,l,m):
    return sub(add(scale(r[0],sub(scale(m[1],l[2]),scale(l[1],m[2]))),
                   scale(r[1],sub(scale(l[0],m[2]),scale(m[0],l[2])))),
               scale(det(l,m),r[2]))

def enclosure(f):
    return (sum(c*(LO[i] if c>=0 else HI[i]) for i,c in enumerate(f)),
            sum(c*(HI[i] if c>=0 else LO[i]) for i,c in enumerate(f)))

def nonzero(f):
    lo,hi=enclosure(f)
    return lo>0 or hi<0 or (f[9]!=0 and all(c==0 for c in f[:9]))

LO=[F(bounds[k][0],scales[k]) for k in range(1,10)]+[F(0)]
HI=[F(bounds[k][1],scales[k]) for k in range(1,10)]+[EPS]
MID=[(a+b)/2 for a,b in zip(LO,HI)]
MID[9]=EPS

old=[(F(0),F(-1),form())]
ks=[8,6,4,2,10,10,2,4,6,8]
ss=[-1]*5+[1]*5
old += [(1/v,F(-1),form(k-1,s/v)) for k,s,v in zip(ks,ss,V)]
bb=[-tan_pi(k,20).midpoint() for k in [9,7,5,3,1]]+[tan_pi(k,20).midpoint() for k in [1,3,5,7,9]]
mm=[F(2,3*10**10)*(2*b/(1+b*b)+F(1,10**6)/b) for b in bb]
SLOPE_SCALE=10**35
mm=[F((m*SLOPE_SCALE).numerator//(m*SLOPE_SCALE).denominator,SLOPE_SCALE) for m in mm]
new=[(m,F(-1),form(k-1,m*s)) for m,k,s in zip(mm,[9,7,5,3,1,1,3,5,7,9],[-1]*5+[1]*5)]
LINES=old+new
refs=[primitive((a,b,sum(c*x for c,x in zip(f,MID)))) for a,b,f in LINES]
ar=arrangement(refs)
assert len(ar['triangles'])==132
TRIS=sorted(ar['triangles'])
assert len(TRIS)==len(set(TRIS))
DIST=[t for t in TRIS if 0 in t]
assert len(DIST)==19
VISIBLE=[(0,20,21),(1,3,21),(2,4,21),(5,7,21),(6,8,21),(10,13,21),
         (11,15,21),(12,14,21),(16,19,21),(17,18,21)]

def check():
    for i,j in combinations(range(21),2):assert det(LINES[i],LINES[j])
    for i,j,k in combinations(range(21),3):assert nonzero(evaluate_form(LINES[k],LINES[i],LINES[j])),(i,j,k)
    for t in TRIS:
        for r in range(21):
            boxes=[]
            for i,j in combinations(t,2):
                boxes.append(enclosure(scale(det(LINES[i],LINES[j]),evaluate_form(LINES[r],LINES[i],LINES[j]))))
            assert all(a>=0 for a,b in boxes) or all(b<=0 for a,b in boxes),(t,r)
    for i,j,k in VISIBLE:
        for r in range(21):
            a,b=enclosure(scale(det(LINES[i],LINES[j]),evaluate_form(LINES[r],LINES[i],LINES[j])))
            ds=[det(LINES[r],LINES[s])*(10*LINES[s][1]+13*LINES[s][0]) for s in (i,j)]
            assert a>=0 and all(x>=0 for x in ds) or b<=0 and all(x<=0 for x in ds),(i,j,r)

def write():
    check()
    DEST=ROOT/'experiments/2026-09-21/hybrid-family'
    DEST.mkdir(parents=True,exist_ok=True)
    cert=dict(n=21,triangle_count=132,lines_frac=[[str(x) for x in line] for line in refs],
              construction='Rational reference for a uniformly certified true tangent-grid seed with rational slopes',
              priority_status='Known count; new formal parameter/boundary compatibility certificate')
    path=DEST/'seed21-reference.json'
    path.write_text(json.dumps(cert,indent=2)+'\n',encoding='utf-8')
    independent=verify(path)
    def vec(xs):return '!['+','.join(qstr(x) for x in xs)+']'
    def triple(ts):return '['+','.join('⟨'+','.join(map(str,t))+'⟩' for t in ts)+']'
    lean='''import Kobon.HybridBoundary
import Kobon.BBLExtrema
import Kobon.BBLTangentBounds
import Mathlib.Tactic.FinCases

/-! A complete real-parameter 21-line seed certificate.
The rational slopes are fixed. The intercepts are actual tan(k*pi/20).
The finite box checks use native_decide; geometry and trigonometric bounds are
proved by the generic soundness theorems. This does not formalize BBL doubling.
-/
namespace Kobon.BBLSeed21
open Parametric Exterior HybridBoundary BBLExtrema Real
set_option maxRecDepth 100000
set_option maxHeartbeats 0
'''
    lean+=f'\ndef lo : Form 10 := {vec(LO)}\ndef hi : Form 10 := {vec(HI)}\n'
    lean+='\ndef lines : Array (ParamLine 10) := #[\n'+',\n'.join('  ⟨'+qstr(a)+','+qstr(b)+','+vec(f)+'⟩' for a,b,f in LINES)+']\n'
    lean+='\ndef lineAt (i : Nat) : ParamLine 10 := lines[i]!\n'
    lean+=f'\ndef triangles : List Triple := {triple(TRIS)}\n'
    lean+=f'\ndef distinguished : List Triple := {triple(DIST)}\n'
    lean+=f'\ndef visible : List Triple := {triple(VISIBLE)}\n'
    lean+=f'\ndef rightSlope : ℚ := {qstr(mm[-1])}\n'
    lean+='''
theorem directions : DirectionCheck 21 lineAt := by native_decide
theorem simple : SimpleCheck 21 lo hi 9 lineAt := by native_decide
theorem triangle_checks :
    triangles.all (fun t => decide (TriangleCheck 21 lo hi lineAt t))=true := by native_decide
theorem distinguished_checks :
    distinguished.all (fun t => decide (TriangleCheck 21 lo hi lineAt t))=true := by native_decide
theorem ordered : Increasing 21 triangles := by decide +kernel
theorem admissible_check : AdmissibleCheck 21 lineAt 10 (-13) := by native_decide
theorem visible_checks :
    visible.all (fun t => decide (VisibleCheck 21 lo hi lineAt 10 (-13) t))=true := by native_decide

noncomputable def parameters (epsilon : ℝ) : Fin 10 → ℝ :=
  ![tan (1*π/20),tan (2*π/20),tan (3*π/20),tan (4*π/20),tan (5*π/20),
    tan (6*π/20),tan (7*π/20),tan (8*π/20),tan (9*π/20),epsilon]

noncomputable def arrangement (epsilon : ℝ) (i : Nat) : Line ℝ :=
  toLine (lineAt i) (parameters epsilon)

theorem parameters_in_box (epsilon : ℝ) (he : 0<epsilon) (hu : epsilon≤1/100000) :
    InBox lo hi (parameters epsilon) := by
  intro i
  fin_cases i
'''
    for k in range(1,10):lean+=f'  · convert BBLTangentBounds.tan_{k}_bounds using 1 <;> norm_num [lo,hi,parameters]\n'
    lean+='''  · simpa [lo,hi,parameters] using And.intro (le_of_lt he) hu

theorem no_parallel (epsilon : ℝ) : NoParallel 21 (arrangement epsilon) :=
  directions_sound 21 lineAt (parameters epsilon) directions

theorem no_concurrent (epsilon : ℝ) (he : 0<epsilon) (hu : epsilon≤1/100000) :
    NoConcurrent 21 (arrangement epsilon) := by
  exact simple_sound 21 lo hi 9 lineAt (parameters epsilon)
    (parameters_in_box epsilon he hu) (by simpa [parameters] using he) simple

theorem all_triangles (epsilon : ℝ) (he : 0<epsilon) (hu : epsilon≤1/100000)
    (t : Triple) (ht : t∈triangles) : TrianglePredicate 21 (arrangement epsilon) t := by
  have hc := triangle_checks
  simp only [List.all_eq_true,decide_eq_true_eq] at hc
  exact triangle_sound 21 lo hi 9 lineAt (parameters epsilon)
    (parameters_in_box epsilon he hu) (by simpa [parameters] using he) simple t (hc t ht)

theorem all_visible (epsilon : ℝ) (he : 0<epsilon) (hu : epsilon≤1/100000)
    (t : Triple) (ht : t∈visible) :
    VisiblePair 21 (arrangement epsilon) (normalLine 10 (-13)) t := by
  have hc := visible_checks
  simp only [List.all_eq_true,decide_eq_true_eq] at hc
  exact visible_sound 21 lo hi lineAt 10 (-13) (parameters epsilon)
    (parameters_in_box epsilon he hu) directions admissible_check t (hc t ht)

theorem all_distinguished (epsilon : ℝ) (he : 0<epsilon) (hu : epsilon≤1/100000)
    (t : Triple) (ht : t∈distinguished) : TrianglePredicate 21 (arrangement epsilon) t := by
  have hc := distinguished_checks
  simp only [List.all_eq_true,decide_eq_true_eq] at hc
  exact triangle_sound 21 lo hi 9 lineAt (parameters epsilon)
    (parameters_in_box epsilon he hu) (by simpa [parameters] using he) simple t (hc t ht)

theorem distinguished_count : distinguished.length=19 ∧ distinguished.Nodup := by decide +kernel
theorem visible_count : visible.length=10 ∧ visible.Nodup := by decide +kernel

theorem zero_line (epsilon : ℝ) : arrangement epsilon 0=graphLine 0 0 := by
  norm_num [arrangement,toLine,lineAt,lines,graphLine,evaluate,Fin.sum_univ_succ]

theorem last_line (epsilon : ℝ) :
    arrangement epsilon 20=graphLine rightSlope (tan (9*π/20)) := by
  norm_num [arrangement,toLine,lineAt,lines,graphLine,evaluate,Fin.sum_univ_succ,
    rightSlope,parameters]

theorem right_slope_positive : (0:ℝ)<rightSlope := by norm_num [rightSlope]
theorem right_slope_small : (rightSlope:ℝ)<10/13 := by norm_num [rightSlope]

theorem last_intersection (epsilon : ℝ) :
    intersection (arrangement epsilon 0) (arrangement epsilon 20)=(tan (9*π/20),0) := by
  rw [zero_line,last_line]
  have hm : (rightSlope:ℝ) ≠ 0 := ne_of_gt right_slope_positive
  simp [intersection,vertex,graphLine,det,hm]

theorem rightmost_last (epsilon : ℝ) (he : 0<epsilon) (hu : epsilon≤1/100000)
    (r : Fin 21) (hr : r.val ≠ 20) :
    (intersection (arrangement epsilon 20) (arrangement epsilon r)).1≤tan (9*π/20) := by
  let L := arrangement epsilon
  let w := normalLine 10 (-13)
  have hp := no_parallel epsilon
  have hw : Admissible 21 L w := admissible_sound 21 lineAt 10 (-13) (parameters epsilon) admissible_check
  have hv : VisiblePair 21 L w ⟨0,20,21⟩ := all_visible epsilon he hu _ (by simp [visible])
  have hle := visible_extremal_right 21 L w hp hw ⟨0,20,21⟩ hv r hr
  have hdr : det (L 20) (L r) ≠ 0 := det_ne_of_ne 21 L hp ⟨20,by decide⟩ r (by
    intro hh
    exact hr (congrArg Fin.val hh).symm)
  have hdp : det (L 0) (L 20) ≠ 0 := hp ⟨0,by decide⟩ ⟨20,by decide⟩ (by decide)
  have hpr := intersection_on_left (L 20) (L r) hdr
  have hpp := intersection_on_right (L 0) (L 20) hdp
  have hlast : L 20=graphLine rightSlope (tan (9*π/20)) := last_line epsilon
  have hpr' : affineEval (graphLine rightSlope (tan (9*π/20))) (intersection (L 20) (L r))=0 := by
    rw [← hlast]
    exact hpr
  have hpp' : affineEval (graphLine rightSlope (tan (9*π/20))) (intersection (L 0) (L 20))=0 := by
    rw [← hlast]
    exact hpp
  have hdir : 0<w.a+w.b*(rightSlope:ℝ) := by
    dsimp [w,normalLine]
    norm_num [rightSlope]
  have hh := graph_projection_order rightSlope (tan (9*π/20)) w _ _ hpr' hpp' hdir hle
  simpa only [L,last_intersection,Prod.fst] using hh

theorem simple_lower_bound (epsilon : ℝ) (he : 0<epsilon) (hu : epsilon≤1/100000) :
    SimpleLowerBound 21 132 := by
  exact ⟨arrangement epsilon,no_parallel epsilon,no_concurrent epsilon he hu,
    triangles,increasing_nodup 21 triangles ordered,all_triangles epsilon he hu,by decide⟩

theorem exterior_lower_bound (epsilon : ℝ) (he : 0<epsilon) (hu : epsilon≤1/100000) :
    SimpleLowerBound 22 142 := by
  let L := arrangement epsilon
  let w := normalLine 10 (-13)
  have hw : Admissible 21 L w := admissible_sound 21 lineAt 10 (-13) (parameters epsilon) admissible_check
  have h := Exterior.extension 21 132 L triangles visible w (safeHeight 21 L w)
    (no_parallel epsilon) (no_concurrent epsilon he hu)
    (increasing_nodup 21 triangles ordered) (all_triangles epsilon he hu) (by decide)
    (by decide +kernel) (all_visible epsilon he hu) hw (safeHeight_beyond 21 L w)
  simpa [visible] using h

theorem arbitrarily_small (eta : ℝ) (heta : 0<eta) :
    ∃ epsilon : ℝ, 0<epsilon ∧ epsilon<eta ∧ epsilon≤1/100000 ∧
      NoConcurrent 21 (arrangement epsilon) ∧
      (∀ t∈triangles, TrianglePredicate 21 (arrangement epsilon) t) ∧
      (∀ t∈visible, VisiblePair 21 (arrangement epsilon) (normalLine 10 (-13)) t) := by
  let epsilon := min (eta/2) (1/100000:ℝ)
  have he : 0<epsilon := lt_min (by linarith) (by norm_num)
  have hu : epsilon≤1/100000 := min_le_right _ _
  have hl : epsilon<eta := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  exact ⟨epsilon,he,hl,hu,no_concurrent epsilon he hu,all_triangles epsilon he hu,all_visible epsilon he hu⟩

#print axioms simple_lower_bound
#print axioms exterior_lower_bound
#print axioms arbitrarily_small
#print axioms rightmost_last
end Kobon.BBLSeed21
'''
    (ROOT/'Kobon/BBLSeed21.lean').write_text(lean,encoding='utf-8')
    report=dict(reference=independent,parametric_triangles=132,distinguished_triangles=19,
                visible_pairs=10,epsilon_interval='0<epsilon<=1/100000',
                method='Exact rational box verification; generated Lean module separately checked',
                slopes=[str(m) for m in mm])
    (Path(__file__).parent/'seed21-verification.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(report,indent=2))

if __name__=='__main__':write()
