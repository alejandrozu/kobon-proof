import Kobon.OpenMathConstructionSeed37Checks
import Kobon.BBLTangent36Bounds
namespace Kobon.OpenMathConstructionSeed37
open Parametric Exterior HybridBoundary BBLExtrema Real
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def parameters (epsilon : ℝ) : Fin 18 → ℝ := ![tan (1*π/36),tan (2*π/36),tan (3*π/36),tan (4*π/36),tan (5*π/36),tan (6*π/36),tan (7*π/36),tan (8*π/36),tan (9*π/36),tan (10*π/36),tan (11*π/36),tan (12*π/36),tan (13*π/36),tan (14*π/36),tan (15*π/36),tan (16*π/36),tan (17*π/36),epsilon]
noncomputable def arrangement (epsilon : ℝ) (i : Nat) : Line ℝ :=
  toLine (lineAt i) (parameters epsilon)
theorem parameters_in_box (epsilon : ℝ) (he : 0<epsilon) (hu : epsilon≤(1/100000000)) :
    InBox lo hi (parameters epsilon) := by
  intro i
  fin_cases i
  · have h := BBLTangent36Bounds.tan_1_bounds
    try simp only [one_mul] at h
    norm_num [lo,hi,parameters,OpenMathIntegerBoxes.grid,OpenMathConstructionSeed37Fast.gridDen,
      OpenMathConstructionSeed37Fast.loInt,OpenMathConstructionSeed37Fast.hiInt,OpenMathConstructionSeed37Fast.loInts,OpenMathConstructionSeed37Fast.hiInts]
    constructor <;> linarith [h.1,h.2]
  · have h := BBLTangent36Bounds.tan_2_bounds
    try simp only [one_mul] at h
    norm_num [lo,hi,parameters,OpenMathIntegerBoxes.grid,OpenMathConstructionSeed37Fast.gridDen,
      OpenMathConstructionSeed37Fast.loInt,OpenMathConstructionSeed37Fast.hiInt,OpenMathConstructionSeed37Fast.loInts,OpenMathConstructionSeed37Fast.hiInts]
    constructor <;> linarith [h.1,h.2]
  · have h := BBLTangent36Bounds.tan_3_bounds
    try simp only [one_mul] at h
    norm_num [lo,hi,parameters,OpenMathIntegerBoxes.grid,OpenMathConstructionSeed37Fast.gridDen,
      OpenMathConstructionSeed37Fast.loInt,OpenMathConstructionSeed37Fast.hiInt,OpenMathConstructionSeed37Fast.loInts,OpenMathConstructionSeed37Fast.hiInts]
    constructor <;> linarith [h.1,h.2]
  · have h := BBLTangent36Bounds.tan_4_bounds
    try simp only [one_mul] at h
    norm_num [lo,hi,parameters,OpenMathIntegerBoxes.grid,OpenMathConstructionSeed37Fast.gridDen,
      OpenMathConstructionSeed37Fast.loInt,OpenMathConstructionSeed37Fast.hiInt,OpenMathConstructionSeed37Fast.loInts,OpenMathConstructionSeed37Fast.hiInts]
    constructor <;> linarith [h.1,h.2]
  · have h := BBLTangent36Bounds.tan_5_bounds
    try simp only [one_mul] at h
    norm_num [lo,hi,parameters,OpenMathIntegerBoxes.grid,OpenMathConstructionSeed37Fast.gridDen,
      OpenMathConstructionSeed37Fast.loInt,OpenMathConstructionSeed37Fast.hiInt,OpenMathConstructionSeed37Fast.loInts,OpenMathConstructionSeed37Fast.hiInts]
    constructor <;> linarith [h.1,h.2]
  · have h := BBLTangent36Bounds.tan_6_bounds
    try simp only [one_mul] at h
    norm_num [lo,hi,parameters,OpenMathIntegerBoxes.grid,OpenMathConstructionSeed37Fast.gridDen,
      OpenMathConstructionSeed37Fast.loInt,OpenMathConstructionSeed37Fast.hiInt,OpenMathConstructionSeed37Fast.loInts,OpenMathConstructionSeed37Fast.hiInts]
    constructor <;> linarith [h.1,h.2]
  · have h := BBLTangent36Bounds.tan_7_bounds
    try simp only [one_mul] at h
    norm_num [lo,hi,parameters,OpenMathIntegerBoxes.grid,OpenMathConstructionSeed37Fast.gridDen,
      OpenMathConstructionSeed37Fast.loInt,OpenMathConstructionSeed37Fast.hiInt,OpenMathConstructionSeed37Fast.loInts,OpenMathConstructionSeed37Fast.hiInts]
    constructor <;> linarith [h.1,h.2]
  · have h := BBLTangent36Bounds.tan_8_bounds
    try simp only [one_mul] at h
    norm_num [lo,hi,parameters,OpenMathIntegerBoxes.grid,OpenMathConstructionSeed37Fast.gridDen,
      OpenMathConstructionSeed37Fast.loInt,OpenMathConstructionSeed37Fast.hiInt,OpenMathConstructionSeed37Fast.loInts,OpenMathConstructionSeed37Fast.hiInts]
    constructor <;> linarith [h.1,h.2]
  · have h := BBLTangent36Bounds.tan_9_bounds
    try simp only [one_mul] at h
    norm_num [lo,hi,parameters,OpenMathIntegerBoxes.grid,OpenMathConstructionSeed37Fast.gridDen,
      OpenMathConstructionSeed37Fast.loInt,OpenMathConstructionSeed37Fast.hiInt,OpenMathConstructionSeed37Fast.loInts,OpenMathConstructionSeed37Fast.hiInts]
    constructor <;> linarith [h.1,h.2]
  · have h := BBLTangent36Bounds.tan_10_bounds
    try simp only [one_mul] at h
    norm_num [lo,hi,parameters,OpenMathIntegerBoxes.grid,OpenMathConstructionSeed37Fast.gridDen,
      OpenMathConstructionSeed37Fast.loInt,OpenMathConstructionSeed37Fast.hiInt,OpenMathConstructionSeed37Fast.loInts,OpenMathConstructionSeed37Fast.hiInts]
    constructor <;> linarith [h.1,h.2]
  · have h := BBLTangent36Bounds.tan_11_bounds
    try simp only [one_mul] at h
    norm_num [lo,hi,parameters,OpenMathIntegerBoxes.grid,OpenMathConstructionSeed37Fast.gridDen,
      OpenMathConstructionSeed37Fast.loInt,OpenMathConstructionSeed37Fast.hiInt,OpenMathConstructionSeed37Fast.loInts,OpenMathConstructionSeed37Fast.hiInts]
    constructor <;> linarith [h.1,h.2]
  · have h := BBLTangent36Bounds.tan_12_bounds
    try simp only [one_mul] at h
    norm_num [lo,hi,parameters,OpenMathIntegerBoxes.grid,OpenMathConstructionSeed37Fast.gridDen,
      OpenMathConstructionSeed37Fast.loInt,OpenMathConstructionSeed37Fast.hiInt,OpenMathConstructionSeed37Fast.loInts,OpenMathConstructionSeed37Fast.hiInts]
    constructor <;> linarith [h.1,h.2]
  · have h := BBLTangent36Bounds.tan_13_bounds
    try simp only [one_mul] at h
    norm_num [lo,hi,parameters,OpenMathIntegerBoxes.grid,OpenMathConstructionSeed37Fast.gridDen,
      OpenMathConstructionSeed37Fast.loInt,OpenMathConstructionSeed37Fast.hiInt,OpenMathConstructionSeed37Fast.loInts,OpenMathConstructionSeed37Fast.hiInts]
    constructor <;> linarith [h.1,h.2]
  · have h := BBLTangent36Bounds.tan_14_bounds
    try simp only [one_mul] at h
    norm_num [lo,hi,parameters,OpenMathIntegerBoxes.grid,OpenMathConstructionSeed37Fast.gridDen,
      OpenMathConstructionSeed37Fast.loInt,OpenMathConstructionSeed37Fast.hiInt,OpenMathConstructionSeed37Fast.loInts,OpenMathConstructionSeed37Fast.hiInts]
    constructor <;> linarith [h.1,h.2]
  · have h := BBLTangent36Bounds.tan_15_bounds
    try simp only [one_mul] at h
    norm_num [lo,hi,parameters,OpenMathIntegerBoxes.grid,OpenMathConstructionSeed37Fast.gridDen,
      OpenMathConstructionSeed37Fast.loInt,OpenMathConstructionSeed37Fast.hiInt,OpenMathConstructionSeed37Fast.loInts,OpenMathConstructionSeed37Fast.hiInts]
    constructor <;> linarith [h.1,h.2]
  · have h := BBLTangent36Bounds.tan_16_bounds
    try simp only [one_mul] at h
    norm_num [lo,hi,parameters,OpenMathIntegerBoxes.grid,OpenMathConstructionSeed37Fast.gridDen,
      OpenMathConstructionSeed37Fast.loInt,OpenMathConstructionSeed37Fast.hiInt,OpenMathConstructionSeed37Fast.loInts,OpenMathConstructionSeed37Fast.hiInts]
    constructor <;> linarith [h.1,h.2]
  · have h := BBLTangent36Bounds.tan_17_bounds
    try simp only [one_mul] at h
    norm_num [lo,hi,parameters,OpenMathIntegerBoxes.grid,OpenMathConstructionSeed37Fast.gridDen,
      OpenMathConstructionSeed37Fast.loInt,OpenMathConstructionSeed37Fast.hiInt,OpenMathConstructionSeed37Fast.loInts,OpenMathConstructionSeed37Fast.hiInts]
    constructor <;> linarith [h.1,h.2]
  · norm_num [lo,hi,parameters,OpenMathIntegerBoxes.grid,OpenMathConstructionSeed37Fast.gridDen,
      OpenMathConstructionSeed37Fast.loInt,OpenMathConstructionSeed37Fast.hiInt,OpenMathConstructionSeed37Fast.loInts,OpenMathConstructionSeed37Fast.hiInts]
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
end Kobon.OpenMathConstructionSeed37
