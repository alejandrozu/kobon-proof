import Kobon.HybridBoundary
import Kobon.BBLExtrema
import Mathlib.Tactic.FinCases

/-! A compatible seed for the classical optimal dyadic family.
The inequalities 5:5 and 6:7 are classical; the parameter and visibility
certificates provide actual geometry for a future general doubling theorem. -/
namespace Kobon.TamuraSeed5
open Parametric Exterior HybridBoundary BBLExtrema
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def lo : Form 2 := ![1,0]
def hi : Form 2 := ![1,1/100000]
def lines : Array (ParamLine 2) := #[
  ⟨0,-1,![0,0]⟩,⟨-1/15,-1,![1/15,0]⟩,⟨1/10,-1,![0,-1/10]⟩,
  ⟨-1/10,-1,![0,-1/10]⟩,⟨1/30,-1,![1/30,0]⟩]
def lineAt (i : ℕ) : ParamLine 2 := lines[i]!
def triangles : List Triple := [⟨0,1,2⟩,⟨0,2,3⟩,⟨0,3,4⟩,⟨1,2,4⟩,⟨1,3,4⟩]
def visible : List Triple := [⟨0,4,5⟩,⟨1,3,5⟩]

theorem directions : DirectionCheck 5 lineAt := by decide +kernel
theorem simple : SimpleCheck 5 lo hi 1 lineAt := by decide +kernel
theorem ordered : Increasing 5 triangles := by decide +kernel
theorem triangle_checks :
    triangles.all (fun t => decide (TriangleCheck 5 lo hi lineAt t))=true := by decide +kernel
theorem distinguished_checks : ∀ i : Fin 3,
    TriangleCheck 5 lo hi lineAt ⟨0,i.val+1,i.val+2⟩ := by decide +kernel
theorem admissible_check : AdmissibleCheck 5 lineAt 10 (-13) := by decide +kernel
theorem visible_checks :
    visible.all (fun t => decide (VisibleCheck 5 lo hi lineAt 10 (-13) t))=true := by decide +kernel

noncomputable def parameters (epsilon : ℝ) : Fin 2 → ℝ := ![1,epsilon]
noncomputable def arrangement (epsilon : ℝ) (i : ℕ) : Line ℝ :=
  toLine (lineAt i) (parameters epsilon)

theorem parameters_in_box (epsilon : ℝ) (he : 0<epsilon) (hu : epsilon≤1/100000) :
    InBox lo hi (parameters epsilon) := by
  intro i
  fin_cases i
  · norm_num [lo,hi,parameters]
  · simpa [lo,hi,parameters] using And.intro he.le hu

theorem no_parallel (epsilon : ℝ) : NoParallel 5 (arrangement epsilon) :=
  directions_sound 5 lineAt (parameters epsilon) directions

theorem no_concurrent (epsilon : ℝ) (he : 0<epsilon) (hu : epsilon≤1/100000) :
    NoConcurrent 5 (arrangement epsilon) :=
  simple_sound 5 lo hi 1 lineAt (parameters epsilon) (parameters_in_box epsilon he hu)
    (by simpa [parameters] using he) simple

theorem all_triangles (epsilon : ℝ) (he : 0<epsilon) (hu : epsilon≤1/100000)
    (t : Triple) (ht : t∈triangles) : TrianglePredicate 5 (arrangement epsilon) t := by
  have hc := triangle_checks
  simp only [List.all_eq_true,decide_eq_true_eq] at hc
  exact triangle_sound 5 lo hi 1 lineAt (parameters epsilon) (parameters_in_box epsilon he hu)
    (by simpa [parameters] using he) simple t (hc t ht)

theorem all_distinguished (epsilon : ℝ) (he : 0<epsilon) (hu : epsilon≤1/100000)
    (i : Fin 3) : TrianglePredicate 5 (arrangement epsilon) ⟨0,i.val+1,i.val+2⟩ :=
  triangle_sound 5 lo hi 1 lineAt (parameters epsilon) (parameters_in_box epsilon he hu)
    (by simpa [parameters] using he) simple _ (distinguished_checks i)

theorem all_visible (epsilon : ℝ) (he : 0<epsilon) (hu : epsilon≤1/100000)
    (t : Triple) (ht : t∈visible) :
    VisiblePair 5 (arrangement epsilon) (normalLine 10 (-13)) t := by
  have hc := visible_checks
  simp only [List.all_eq_true,decide_eq_true_eq] at hc
  exact visible_sound 5 lo hi lineAt 10 (-13) (parameters epsilon)
    (parameters_in_box epsilon he hu) directions admissible_check t (hc t ht)

theorem zero_line (epsilon : ℝ) : arrangement epsilon 0=graphLine 0 0 := by
  norm_num [arrangement,toLine,lineAt,lines,graphLine,evaluate,Fin.sum_univ_succ]

theorem last_line (epsilon : ℝ) : arrangement epsilon 4=graphLine (1/30) 1 := by
  norm_num [arrangement,toLine,lineAt,lines,graphLine,evaluate,Fin.sum_univ_succ,parameters]

theorem central_lines (epsilon : ℝ) :
    arrangement epsilon 2=graphLine (1/10) (-epsilon) ∧
    arrangement epsilon 3=graphLine (-1/10) epsilon := by
  constructor <;> norm_num [arrangement,toLine,lineAt,lines,graphLine,evaluate,Fin.sum_univ_succ,parameters]
  <;> ring

theorem last_intersection (epsilon : ℝ) :
    intersection (arrangement epsilon 0) (arrangement epsilon 4)=(1,0) := by
  rw [zero_line,last_line]
  norm_num [intersection,vertex,graphLine,det]

theorem rightmost_last (epsilon : ℝ) (he : 0<epsilon) (hu : epsilon≤1/100000)
    (r : Fin 5) (hr : r.val≠4) :
    (intersection (arrangement epsilon 4) (arrangement epsilon r)).1≤1 := by
  let L := arrangement epsilon
  let w := normalLine 10 (-13)
  have hp := no_parallel epsilon
  have hw : Admissible 5 L w := admissible_sound 5 lineAt 10 (-13) (parameters epsilon) admissible_check
  have hv : VisiblePair 5 L w ⟨0,4,5⟩ := all_visible epsilon he hu _ (by simp [visible])
  have hle := visible_extremal_right 5 L w hp hw ⟨0,4,5⟩ hv r hr
  have hdr : det (L 4) (L r)≠0 := det_ne_of_ne 5 L hp ⟨4,by decide⟩ r (by
    intro hh
    exact hr (congrArg Fin.val hh).symm)
  have hdp : det (L 0) (L 4)≠0 := hp ⟨0,by decide⟩ ⟨4,by decide⟩ (by decide)
  have hpr := intersection_on_left (L 4) (L r) hdr
  have hpp := intersection_on_right (L 0) (L 4) hdp
  have hlast : L 4=graphLine (1/30) 1 := last_line epsilon
  have hpr' : affineEval (graphLine (1/30) 1) (intersection (L 4) (L r))=0 := by
    rw [← hlast]; exact hpr
  have hpp' : affineEval (graphLine (1/30) 1) (intersection (L 0) (L 4))=0 := by
    rw [← hlast]; exact hpp
  have hdir : 0<w.a+w.b*(1/30:ℝ) := by norm_num [w,normalLine]
  have hh := graph_projection_order (1/30) 1 w _ _ hpr' hpp' hdir hle
  simpa only [L,last_intersection,Prod.fst] using hh

theorem simple_lower_bound (epsilon : ℝ) (he : 0<epsilon) (hu : epsilon≤1/100000) :
    SimpleLowerBound 5 5 :=
  ⟨arrangement epsilon,no_parallel epsilon,no_concurrent epsilon he hu,triangles,
    increasing_nodup 5 triangles ordered,all_triangles epsilon he hu,by decide⟩

theorem exterior_lower_bound (epsilon : ℝ) (he : 0<epsilon) (hu : epsilon≤1/100000) :
    SimpleLowerBound 6 7 := by
  let L := arrangement epsilon
  let w := normalLine 10 (-13)
  have hw : Admissible 5 L w := admissible_sound 5 lineAt 10 (-13) (parameters epsilon) admissible_check
  have h := Exterior.extension 5 5 L triangles visible w (safeHeight 5 L w)
    (no_parallel epsilon) (no_concurrent epsilon he hu)
    (increasing_nodup 5 triangles ordered) (all_triangles epsilon he hu) (by decide)
    (by decide +kernel) (all_visible epsilon he hu) hw (safeHeight_beyond 5 L w)
  simpa [visible] using h

theorem arbitrarily_small (eta : ℝ) (heta : 0<eta) :
    ∃ epsilon : ℝ, 0<epsilon ∧ epsilon<eta ∧ epsilon≤1/100000 ∧
      NoConcurrent 5 (arrangement epsilon) ∧
      (∀ t∈triangles, TrianglePredicate 5 (arrangement epsilon) t) ∧
      (∀ t∈visible, VisiblePair 5 (arrangement epsilon) (normalLine 10 (-13)) t) := by
  let epsilon := min (eta/2) (1/100000:ℝ)
  have he : 0<epsilon := lt_min (by linarith) (by norm_num)
  have hu : epsilon≤1/100000 := min_le_right _ _
  have hl : epsilon<eta := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  exact ⟨epsilon,he,hl,hu,no_concurrent epsilon he hu,all_triangles epsilon he hu,all_visible epsilon he hu⟩

#print axioms simple_lower_bound
#print axioms exterior_lower_bound
#print axioms arbitrarily_small
#print axioms rightmost_last
end Kobon.TamuraSeed5
