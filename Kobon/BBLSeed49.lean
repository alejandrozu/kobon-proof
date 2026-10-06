import Kobon.BBLSeed49Checks

namespace Kobon.BBLSeed49
open Parametric Exterior HybridBoundary BBLExtrema Real
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem directions : DirectionCheck 49 lineAt := BBLSeed49Checks.directions

theorem simple : SimpleCheck 49 lo hi 23 lineAt := BBLSeed49Checks.simple

theorem triangle_checks :
    triangles.all (fun t => decide (TriangleCheck 49 lo hi lineAt t)) = true :=
  BBLSeed49Checks.triangle_checks

theorem ordered : Increasing 49 triangles := BBLSeed49Checks.ordered

theorem distinguished_subset : ∀ t∈distinguished, t∈triangles :=
  BBLSeed49Checks.distinguished_subset

noncomputable def parameters (epsilon : ℝ) : Fin 24→ℝ := ![tan (1*π/48),tan (2*π/48),tan (3*π/48),tan (4*π/48),tan (5*π/48),tan (6*π/48),tan (7*π/48),tan (8*π/48),tan (9*π/48),tan (10*π/48),tan (11*π/48),tan (12*π/48),tan (13*π/48),tan (14*π/48),tan (15*π/48),tan (16*π/48),tan (17*π/48),tan (18*π/48),tan (19*π/48),tan (20*π/48),tan (21*π/48),tan (22*π/48),tan (23*π/48),epsilon]
noncomputable def arrangement (epsilon : ℝ) (i : Nat) : Line ℝ :=
  toLine (lineAt i) (parameters epsilon)

theorem parameters_in_box (epsilon : ℝ) (he : 0<epsilon) (hu : epsilon≤1/100) :
    InBox lo hi (parameters epsilon) := by
  intro i
  fin_cases i
  · have h := BBLTangent48Bounds.tan_48_1_bounds
    norm_num only [one_mul] at h
    norm_num [lo,hi,parameters]
    constructor <;> linarith [h.1,h.2]
  · have h := BBLTangent48Bounds.tan_48_2_bounds
    norm_num [lo,hi,parameters]
    constructor <;> linarith [h.1,h.2]
  · have h := BBLTangent48Bounds.tan_48_3_bounds
    norm_num [lo,hi,parameters]
    constructor <;> linarith [h.1,h.2]
  · have h := BBLTangent48Bounds.tan_48_4_bounds
    norm_num [lo,hi,parameters]
    constructor <;> linarith [h.1,h.2]
  · have h := BBLTangent48Bounds.tan_48_5_bounds
    norm_num [lo,hi,parameters]
    constructor <;> linarith [h.1,h.2]
  · have h := BBLTangent48Bounds.tan_48_6_bounds
    norm_num [lo,hi,parameters]
    constructor <;> linarith [h.1,h.2]
  · have h := BBLTangent48Bounds.tan_48_7_bounds
    norm_num [lo,hi,parameters]
    constructor <;> linarith [h.1,h.2]
  · have h := BBLTangent48Bounds.tan_48_8_bounds
    norm_num [lo,hi,parameters]
    constructor <;> linarith [h.1,h.2]
  · have h := BBLTangent48Bounds.tan_48_9_bounds
    norm_num [lo,hi,parameters]
    constructor <;> linarith [h.1,h.2]
  · have h := BBLTangent48Bounds.tan_48_10_bounds
    norm_num [lo,hi,parameters]
    constructor <;> linarith [h.1,h.2]
  · have h := BBLTangent48Bounds.tan_48_11_bounds
    norm_num [lo,hi,parameters]
    constructor <;> linarith [h.1,h.2]
  · have h := BBLTangent48Bounds.tan_48_12_bounds
    norm_num [lo,hi,parameters]
    constructor <;> linarith [h.1,h.2]
  · have h := BBLTangent48Bounds.tan_48_13_bounds
    norm_num [lo,hi,parameters]
    constructor <;> linarith [h.1,h.2]
  · have h := BBLTangent48Bounds.tan_48_14_bounds
    norm_num [lo,hi,parameters]
    constructor <;> linarith [h.1,h.2]
  · have h := BBLTangent48Bounds.tan_48_15_bounds
    norm_num [lo,hi,parameters]
    constructor <;> linarith [h.1,h.2]
  · have h := BBLTangent48Bounds.tan_48_16_bounds
    norm_num [lo,hi,parameters]
    constructor <;> linarith [h.1,h.2]
  · have h := BBLTangent48Bounds.tan_48_17_bounds
    norm_num [lo,hi,parameters]
    constructor <;> linarith [h.1,h.2]
  · have h := BBLTangent48Bounds.tan_48_18_bounds
    norm_num [lo,hi,parameters]
    constructor <;> linarith [h.1,h.2]
  · have h := BBLTangent48Bounds.tan_48_19_bounds
    norm_num [lo,hi,parameters]
    constructor <;> linarith [h.1,h.2]
  · have h := BBLTangent48Bounds.tan_48_20_bounds
    norm_num [lo,hi,parameters]
    constructor <;> linarith [h.1,h.2]
  · have h := BBLTangent48Bounds.tan_48_21_bounds
    norm_num [lo,hi,parameters]
    constructor <;> linarith [h.1,h.2]
  · have h := BBLTangent48Bounds.tan_48_22_bounds
    norm_num [lo,hi,parameters]
    constructor <;> linarith [h.1,h.2]
  · have h := BBLTangent48Bounds.tan_48_23_bounds
    norm_num [lo,hi,parameters]
    constructor <;> linarith [h.1,h.2]
  · simpa [lo,hi,parameters] using And.intro (le_of_lt he) hu

theorem no_parallel (epsilon : ℝ) : NoParallel 49 (arrangement epsilon) :=
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
