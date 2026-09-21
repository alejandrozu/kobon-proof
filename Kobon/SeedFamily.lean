import Kobon.Parametric
import Kobon.TangentBounds
import Mathlib.Tactic.FinCases

/-! A whole family of REAL trigonometric seeds, with arbitrarily small positive
exceptional intercepts. The finite rational box checks below use kernel reduction.
The BBL geometric doubling step is not a theorem of this file. -/
namespace Kobon.SeedFamily
open Parametric Real
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def lo : Form 5 := ![(3249/10000),(1453/2000),(6881/5000),(30769/10000),0]
def hi : Form 5 := ![(13/40),(3633/5000),(2753/2000),(30779/10000),(1/100000)]

def lines : Array (ParamLine 5) := #[
  ⟨0,1,![0,0,0,0,0]⟩,
  ⟨1,(-3/2),![0,0,0,-1,0]⟩,
  ⟨1,(1/5),![0,0,-1,0,0]⟩,
  ⟨1,(-7/5),![0,-1,0,0,0]⟩,
  ⟨1,(-1/10),![-1,0,0,0,0]⟩,
  ⟨1,(-2/5),![0,0,0,0,-1]⟩,
  ⟨1,(2/5),![0,0,0,0,1]⟩,
  ⟨1,(-1/2),![1,0,0,0,0]⟩,
  ⟨1,(3/10),![0,1,0,0,0]⟩,
  ⟨1,(-6/5),![0,0,1,0,0]⟩,
  ⟨1,(1/2),![0,0,0,1,0]⟩]

def lineAt (i : Nat) : ParamLine 5 := lines[i]!

def triangles : List Triple := [
  ⟨0,1,2⟩,
  ⟨0,2,3⟩,
  ⟨0,3,4⟩,
  ⟨0,4,5⟩,
  ⟨0,5,6⟩,
  ⟨0,6,7⟩,
  ⟨0,7,8⟩,
  ⟨0,8,9⟩,
  ⟨0,9,10⟩,
  ⟨1,2,6⟩,
  ⟨1,3,9⟩,
  ⟨1,4,6⟩,
  ⟨1,4,8⟩,
  ⟨1,5,8⟩,
  ⟨1,5,10⟩,
  ⟨1,7,10⟩,
  ⟨2,4,7⟩,
  ⟨2,5,7⟩,
  ⟨2,5,9⟩,
  ⟨2,6,10⟩,
  ⟨2,8,10⟩,
  ⟨3,4,6⟩,
  ⟨3,5,6⟩,
  ⟨3,5,8⟩,
  ⟨3,7,8⟩,
  ⟨3,7,10⟩,
  ⟨3,9,10⟩,
  ⟨4,5,9⟩,
  ⟨4,7,9⟩,
  ⟨4,8,10⟩,
  ⟨6,7,9⟩,
  ⟨6,8,9⟩]

theorem directions : DirectionCheck 11 lineAt := by decide +kernel
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
