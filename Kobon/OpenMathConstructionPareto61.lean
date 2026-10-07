import Kobon.OpenMathConstructionPareto61Checks
/-! A stronger compatible uniform61-line seed with1190 triangles and29
visible pairs. The1190 point count is credited to Rohith Poola. A nonlocal
reciprocal-slope cap-cone chamber mutation, followed by reflection and shear,
improves the boundary resource from28 to29. Every predicate is independently
replayed over the entire actual true-tangent epsilon box; the point count is
not claimed as a new finite record.
-/
namespace Kobon.OpenMathConstructionPareto61
open Parametric Exterior HybridBoundary BBLExtrema Real
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable def parameters (epsilon : ℝ) : Fin 30 → ℝ :=
  ![tan (1*π/60),tan (2*π/60),tan (3*π/60),tan (4*π/60),tan (5*π/60),tan (6*π/60),tan (7*π/60),tan (8*π/60),tan (9*π/60),tan (10*π/60),tan (11*π/60),tan (12*π/60),tan (13*π/60),tan (14*π/60),tan (15*π/60),tan (16*π/60),tan (17*π/60),tan (18*π/60),tan (19*π/60),tan (20*π/60),tan (21*π/60),tan (22*π/60),tan (23*π/60),tan (24*π/60),tan (25*π/60),tan (26*π/60),tan (27*π/60),tan (28*π/60),tan (29*π/60),epsilon]

noncomputable def arrangement (epsilon : ℝ) (i : Nat) : Line ℝ :=
  toLine (lineAt i) (parameters epsilon)

theorem parameters_in_box (epsilon : ℝ) (he : 0<epsilon) (hu : epsilon≤(1/100000000)) :
    InBox lo hi (parameters epsilon) := by
  intro i
  fin_cases i
  · have h := BBLTangent60Bounds.tan_1_bounds
    try simp only [one_mul] at h
    norm_num [lo,hi,parameters,OpenMathIntegerBoxes.grid,OpenMathConstructionPareto61Fast.gridDen,OpenMathConstructionPareto61Fast.loInt,OpenMathConstructionPareto61Fast.hiInt,OpenMathConstructionPareto61Fast.loInts,OpenMathConstructionPareto61Fast.hiInts]
    constructor <;> linarith [h.1,h.2]
  · have h := BBLTangent60Bounds.tan_2_bounds
    try simp only [one_mul] at h
    norm_num [lo,hi,parameters,OpenMathIntegerBoxes.grid,OpenMathConstructionPareto61Fast.gridDen,OpenMathConstructionPareto61Fast.loInt,OpenMathConstructionPareto61Fast.hiInt,OpenMathConstructionPareto61Fast.loInts,OpenMathConstructionPareto61Fast.hiInts]
    constructor <;> linarith [h.1,h.2]
  · have h := BBLTangent60Bounds.tan_3_bounds
    try simp only [one_mul] at h
    norm_num [lo,hi,parameters,OpenMathIntegerBoxes.grid,OpenMathConstructionPareto61Fast.gridDen,OpenMathConstructionPareto61Fast.loInt,OpenMathConstructionPareto61Fast.hiInt,OpenMathConstructionPareto61Fast.loInts,OpenMathConstructionPareto61Fast.hiInts]
    constructor <;> linarith [h.1,h.2]
  · have h := BBLTangent60Bounds.tan_4_bounds
    try simp only [one_mul] at h
    norm_num [lo,hi,parameters,OpenMathIntegerBoxes.grid,OpenMathConstructionPareto61Fast.gridDen,OpenMathConstructionPareto61Fast.loInt,OpenMathConstructionPareto61Fast.hiInt,OpenMathConstructionPareto61Fast.loInts,OpenMathConstructionPareto61Fast.hiInts]
    constructor <;> linarith [h.1,h.2]
  · have h := BBLTangent60Bounds.tan_5_bounds
    try simp only [one_mul] at h
    norm_num [lo,hi,parameters,OpenMathIntegerBoxes.grid,OpenMathConstructionPareto61Fast.gridDen,OpenMathConstructionPareto61Fast.loInt,OpenMathConstructionPareto61Fast.hiInt,OpenMathConstructionPareto61Fast.loInts,OpenMathConstructionPareto61Fast.hiInts]
    constructor <;> linarith [h.1,h.2]
  · have h := BBLTangent60Bounds.tan_6_bounds
    try simp only [one_mul] at h
    norm_num [lo,hi,parameters,OpenMathIntegerBoxes.grid,OpenMathConstructionPareto61Fast.gridDen,OpenMathConstructionPareto61Fast.loInt,OpenMathConstructionPareto61Fast.hiInt,OpenMathConstructionPareto61Fast.loInts,OpenMathConstructionPareto61Fast.hiInts]
    constructor <;> linarith [h.1,h.2]
  · have h := BBLTangent60Bounds.tan_7_bounds
    try simp only [one_mul] at h
    norm_num [lo,hi,parameters,OpenMathIntegerBoxes.grid,OpenMathConstructionPareto61Fast.gridDen,OpenMathConstructionPareto61Fast.loInt,OpenMathConstructionPareto61Fast.hiInt,OpenMathConstructionPareto61Fast.loInts,OpenMathConstructionPareto61Fast.hiInts]
    constructor <;> linarith [h.1,h.2]
  · have h := BBLTangent60Bounds.tan_8_bounds
    try simp only [one_mul] at h
    norm_num [lo,hi,parameters,OpenMathIntegerBoxes.grid,OpenMathConstructionPareto61Fast.gridDen,OpenMathConstructionPareto61Fast.loInt,OpenMathConstructionPareto61Fast.hiInt,OpenMathConstructionPareto61Fast.loInts,OpenMathConstructionPareto61Fast.hiInts]
    constructor <;> linarith [h.1,h.2]
  · have h := BBLTangent60Bounds.tan_9_bounds
    try simp only [one_mul] at h
    norm_num [lo,hi,parameters,OpenMathIntegerBoxes.grid,OpenMathConstructionPareto61Fast.gridDen,OpenMathConstructionPareto61Fast.loInt,OpenMathConstructionPareto61Fast.hiInt,OpenMathConstructionPareto61Fast.loInts,OpenMathConstructionPareto61Fast.hiInts]
    constructor <;> linarith [h.1,h.2]
  · have h := BBLTangent60Bounds.tan_10_bounds
    try simp only [one_mul] at h
    norm_num [lo,hi,parameters,OpenMathIntegerBoxes.grid,OpenMathConstructionPareto61Fast.gridDen,OpenMathConstructionPareto61Fast.loInt,OpenMathConstructionPareto61Fast.hiInt,OpenMathConstructionPareto61Fast.loInts,OpenMathConstructionPareto61Fast.hiInts]
    constructor <;> linarith [h.1,h.2]
  · have h := BBLTangent60Bounds.tan_11_bounds
    try simp only [one_mul] at h
    norm_num [lo,hi,parameters,OpenMathIntegerBoxes.grid,OpenMathConstructionPareto61Fast.gridDen,OpenMathConstructionPareto61Fast.loInt,OpenMathConstructionPareto61Fast.hiInt,OpenMathConstructionPareto61Fast.loInts,OpenMathConstructionPareto61Fast.hiInts]
    constructor <;> linarith [h.1,h.2]
  · have h := BBLTangent60Bounds.tan_12_bounds
    try simp only [one_mul] at h
    norm_num [lo,hi,parameters,OpenMathIntegerBoxes.grid,OpenMathConstructionPareto61Fast.gridDen,OpenMathConstructionPareto61Fast.loInt,OpenMathConstructionPareto61Fast.hiInt,OpenMathConstructionPareto61Fast.loInts,OpenMathConstructionPareto61Fast.hiInts]
    constructor <;> linarith [h.1,h.2]
  · have h := BBLTangent60Bounds.tan_13_bounds
    try simp only [one_mul] at h
    norm_num [lo,hi,parameters,OpenMathIntegerBoxes.grid,OpenMathConstructionPareto61Fast.gridDen,OpenMathConstructionPareto61Fast.loInt,OpenMathConstructionPareto61Fast.hiInt,OpenMathConstructionPareto61Fast.loInts,OpenMathConstructionPareto61Fast.hiInts]
    constructor <;> linarith [h.1,h.2]
  · have h := BBLTangent60Bounds.tan_14_bounds
    try simp only [one_mul] at h
    norm_num [lo,hi,parameters,OpenMathIntegerBoxes.grid,OpenMathConstructionPareto61Fast.gridDen,OpenMathConstructionPareto61Fast.loInt,OpenMathConstructionPareto61Fast.hiInt,OpenMathConstructionPareto61Fast.loInts,OpenMathConstructionPareto61Fast.hiInts]
    constructor <;> linarith [h.1,h.2]
  · have h := BBLTangent60Bounds.tan_15_bounds
    try simp only [one_mul] at h
    norm_num [lo,hi,parameters,OpenMathIntegerBoxes.grid,OpenMathConstructionPareto61Fast.gridDen,OpenMathConstructionPareto61Fast.loInt,OpenMathConstructionPareto61Fast.hiInt,OpenMathConstructionPareto61Fast.loInts,OpenMathConstructionPareto61Fast.hiInts]
    constructor <;> linarith [h.1,h.2]
  · have h := BBLTangent60Bounds.tan_16_bounds
    try simp only [one_mul] at h
    norm_num [lo,hi,parameters,OpenMathIntegerBoxes.grid,OpenMathConstructionPareto61Fast.gridDen,OpenMathConstructionPareto61Fast.loInt,OpenMathConstructionPareto61Fast.hiInt,OpenMathConstructionPareto61Fast.loInts,OpenMathConstructionPareto61Fast.hiInts]
    constructor <;> linarith [h.1,h.2]
  · have h := BBLTangent60Bounds.tan_17_bounds
    try simp only [one_mul] at h
    norm_num [lo,hi,parameters,OpenMathIntegerBoxes.grid,OpenMathConstructionPareto61Fast.gridDen,OpenMathConstructionPareto61Fast.loInt,OpenMathConstructionPareto61Fast.hiInt,OpenMathConstructionPareto61Fast.loInts,OpenMathConstructionPareto61Fast.hiInts]
    constructor <;> linarith [h.1,h.2]
  · have h := BBLTangent60Bounds.tan_18_bounds
    try simp only [one_mul] at h
    norm_num [lo,hi,parameters,OpenMathIntegerBoxes.grid,OpenMathConstructionPareto61Fast.gridDen,OpenMathConstructionPareto61Fast.loInt,OpenMathConstructionPareto61Fast.hiInt,OpenMathConstructionPareto61Fast.loInts,OpenMathConstructionPareto61Fast.hiInts]
    constructor <;> linarith [h.1,h.2]
  · have h := BBLTangent60Bounds.tan_19_bounds
    try simp only [one_mul] at h
    norm_num [lo,hi,parameters,OpenMathIntegerBoxes.grid,OpenMathConstructionPareto61Fast.gridDen,OpenMathConstructionPareto61Fast.loInt,OpenMathConstructionPareto61Fast.hiInt,OpenMathConstructionPareto61Fast.loInts,OpenMathConstructionPareto61Fast.hiInts]
    constructor <;> linarith [h.1,h.2]
  · have h := BBLTangent60Bounds.tan_20_bounds
    try simp only [one_mul] at h
    norm_num [lo,hi,parameters,OpenMathIntegerBoxes.grid,OpenMathConstructionPareto61Fast.gridDen,OpenMathConstructionPareto61Fast.loInt,OpenMathConstructionPareto61Fast.hiInt,OpenMathConstructionPareto61Fast.loInts,OpenMathConstructionPareto61Fast.hiInts]
    constructor <;> linarith [h.1,h.2]
  · have h := BBLTangent60Bounds.tan_21_bounds
    try simp only [one_mul] at h
    norm_num [lo,hi,parameters,OpenMathIntegerBoxes.grid,OpenMathConstructionPareto61Fast.gridDen,OpenMathConstructionPareto61Fast.loInt,OpenMathConstructionPareto61Fast.hiInt,OpenMathConstructionPareto61Fast.loInts,OpenMathConstructionPareto61Fast.hiInts]
    constructor <;> linarith [h.1,h.2]
  · have h := BBLTangent60Bounds.tan_22_bounds
    try simp only [one_mul] at h
    norm_num [lo,hi,parameters,OpenMathIntegerBoxes.grid,OpenMathConstructionPareto61Fast.gridDen,OpenMathConstructionPareto61Fast.loInt,OpenMathConstructionPareto61Fast.hiInt,OpenMathConstructionPareto61Fast.loInts,OpenMathConstructionPareto61Fast.hiInts]
    constructor <;> linarith [h.1,h.2]
  · have h := BBLTangent60Bounds.tan_23_bounds
    try simp only [one_mul] at h
    norm_num [lo,hi,parameters,OpenMathIntegerBoxes.grid,OpenMathConstructionPareto61Fast.gridDen,OpenMathConstructionPareto61Fast.loInt,OpenMathConstructionPareto61Fast.hiInt,OpenMathConstructionPareto61Fast.loInts,OpenMathConstructionPareto61Fast.hiInts]
    constructor <;> linarith [h.1,h.2]
  · have h := BBLTangent60Bounds.tan_24_bounds
    try simp only [one_mul] at h
    norm_num [lo,hi,parameters,OpenMathIntegerBoxes.grid,OpenMathConstructionPareto61Fast.gridDen,OpenMathConstructionPareto61Fast.loInt,OpenMathConstructionPareto61Fast.hiInt,OpenMathConstructionPareto61Fast.loInts,OpenMathConstructionPareto61Fast.hiInts]
    constructor <;> linarith [h.1,h.2]
  · have h := BBLTangent60Bounds.tan_25_bounds
    try simp only [one_mul] at h
    norm_num [lo,hi,parameters,OpenMathIntegerBoxes.grid,OpenMathConstructionPareto61Fast.gridDen,OpenMathConstructionPareto61Fast.loInt,OpenMathConstructionPareto61Fast.hiInt,OpenMathConstructionPareto61Fast.loInts,OpenMathConstructionPareto61Fast.hiInts]
    constructor <;> linarith [h.1,h.2]
  · have h := BBLTangent60Bounds.tan_26_bounds
    try simp only [one_mul] at h
    norm_num [lo,hi,parameters,OpenMathIntegerBoxes.grid,OpenMathConstructionPareto61Fast.gridDen,OpenMathConstructionPareto61Fast.loInt,OpenMathConstructionPareto61Fast.hiInt,OpenMathConstructionPareto61Fast.loInts,OpenMathConstructionPareto61Fast.hiInts]
    constructor <;> linarith [h.1,h.2]
  · have h := BBLTangent60Bounds.tan_27_bounds
    try simp only [one_mul] at h
    norm_num [lo,hi,parameters,OpenMathIntegerBoxes.grid,OpenMathConstructionPareto61Fast.gridDen,OpenMathConstructionPareto61Fast.loInt,OpenMathConstructionPareto61Fast.hiInt,OpenMathConstructionPareto61Fast.loInts,OpenMathConstructionPareto61Fast.hiInts]
    constructor <;> linarith [h.1,h.2]
  · have h := BBLTangent60Bounds.tan_28_bounds
    try simp only [one_mul] at h
    norm_num [lo,hi,parameters,OpenMathIntegerBoxes.grid,OpenMathConstructionPareto61Fast.gridDen,OpenMathConstructionPareto61Fast.loInt,OpenMathConstructionPareto61Fast.hiInt,OpenMathConstructionPareto61Fast.loInts,OpenMathConstructionPareto61Fast.hiInts]
    constructor <;> linarith [h.1,h.2]
  · have h := BBLTangent60Bounds.tan_29_bounds
    try simp only [one_mul] at h
    norm_num [lo,hi,parameters,OpenMathIntegerBoxes.grid,OpenMathConstructionPareto61Fast.gridDen,OpenMathConstructionPareto61Fast.loInt,OpenMathConstructionPareto61Fast.hiInt,OpenMathConstructionPareto61Fast.loInts,OpenMathConstructionPareto61Fast.hiInts]
    constructor <;> linarith [h.1,h.2]
  · norm_num [lo,hi,parameters,OpenMathIntegerBoxes.grid,OpenMathConstructionPareto61Fast.gridDen,OpenMathConstructionPareto61Fast.loInt,OpenMathConstructionPareto61Fast.hiInt,OpenMathConstructionPareto61Fast.loInts,OpenMathConstructionPareto61Fast.hiInts]
    exact And.intro (le_of_lt he) hu

theorem no_parallel (epsilon : ℝ) : NoParallel 61 (arrangement epsilon) :=
  directions_sound 61 lineAt (parameters epsilon) directions

theorem no_concurrent (epsilon : ℝ) (he : 0<epsilon) (hu : epsilon≤(1/100000000)) :
    NoConcurrent 61 (arrangement epsilon) := by
  exact simple_sound 61 lo hi 29 lineAt (parameters epsilon)
    (parameters_in_box epsilon he hu) (by simpa [parameters] using he) simple

theorem all_triangles (epsilon : ℝ) (he : 0<epsilon) (hu : epsilon≤(1/100000000))
    (t : Triple) (ht : t∈triangles) : TrianglePredicate 61 (arrangement epsilon) t := by
  have hc := triangle_checks
  simp only [List.all_eq_true,decide_eq_true_eq] at hc
  exact triangle_sound 61 lo hi 29 lineAt (parameters epsilon)
    (parameters_in_box epsilon he hu) (by simpa [parameters] using he) simple t (hc t ht)

theorem all_visible (epsilon : ℝ) (he : 0<epsilon) (hu : epsilon≤(1/100000000))
    (t : Triple) (ht : t∈visible) :
    VisiblePair 61 (arrangement epsilon) (normalLine 1 (-8000441397/4000000000)) t := by
  have hc := visible_checks
  simp only [List.all_eq_true,decide_eq_true_eq] at hc
  exact visible_sound 61 lo hi lineAt 1 (-8000441397/4000000000) (parameters epsilon)
    (parameters_in_box epsilon he hu) directions admissible_check t (hc t ht)

theorem all_distinguished (epsilon : ℝ) (he : 0<epsilon) (hu : epsilon≤(1/100000000))
    (t : Triple) (ht : t∈distinguished) : TrianglePredicate 61 (arrangement epsilon) t := by
  have hc := distinguished_checks
  simp only [List.all_eq_true,decide_eq_true_eq] at hc
  exact triangle_sound 61 lo hi 29 lineAt (parameters epsilon)
    (parameters_in_box epsilon he hu) (by simpa [parameters] using he) simple t (hc t ht)

theorem distinguished_count : distinguished.length=59 ∧ distinguished.Nodup := by decide +kernel
theorem visible_count : visible.length=29 ∧ visible.Nodup := by decide +kernel

theorem zero_line (epsilon : ℝ) : arrangement epsilon 0=graphLine 0 0 := by
  norm_num [arrangement,toLine,lineAt,lines,OpenMathConstructionPareto61Fast.lineFactor,OpenMathConstructionPareto61Fast.intLineAt,OpenMathConstructionPareto61Fast.intLines,OpenMathIntegerBoxes.castLine,OpenMathIntegerBoxes.castForm,OpenMathConstructionRescale.rescale,Parametric.scale,graphLine,evaluate,Fin.sum_univ_succ]

theorem last_line (epsilon : ℝ) :
    arrangement epsilon 60=graphLine rightSlope (tan (29*π/60)) := by
  norm_num [arrangement,toLine,lineAt,lines,OpenMathConstructionPareto61Fast.lineFactor,OpenMathConstructionPareto61Fast.intLineAt,OpenMathConstructionPareto61Fast.intLines,OpenMathIntegerBoxes.castLine,OpenMathIntegerBoxes.castForm,OpenMathConstructionRescale.rescale,Parametric.scale,graphLine,evaluate,Fin.sum_univ_succ,
    rightSlope,parameters]

theorem right_slope_positive : (0:ℝ)<rightSlope := by norm_num [rightSlope]
theorem right_slope_small : (rightSlope:ℝ)<10/13 := by norm_num [rightSlope]

theorem last_intersection (epsilon : ℝ) :
    intersection (arrangement epsilon 0) (arrangement epsilon 60)=(tan (29*π/60),0) := by
  rw [zero_line,last_line]
  have hm : (rightSlope:ℝ) ≠ 0 := ne_of_gt right_slope_positive
  simp [intersection,vertex,graphLine,det,hm]

theorem rightmost_last (epsilon : ℝ) (he : 0<epsilon) (hu : epsilon≤(1/100000000))
    (r : Fin 61) (hr : r.val ≠ 60) :
    (intersection (arrangement epsilon 60) (arrangement epsilon r)).1≤tan (29*π/60) := by
  let L := arrangement epsilon
  let w := normalLine 1 (-8000441397/4000000000)
  have hp := no_parallel epsilon
  have hw : Admissible 61 L w := admissible_sound 61 lineAt 1 (-8000441397/4000000000) (parameters epsilon) admissible_check
  have hv : VisiblePair 61 L w ⟨0,60,61⟩ := all_visible epsilon he hu _ (by simp [visible])
  have hle := visible_extremal_right 61 L w hp hw ⟨0,60,61⟩ hv r hr
  have hdr : det (L 60) (L r) ≠ 0 := det_ne_of_ne 61 L hp ⟨60,by decide⟩ r (by
    intro hh
    exact hr (congrArg Fin.val hh).symm)
  have hdp : det (L 0) (L 60) ≠ 0 := hp ⟨0,by decide⟩ ⟨60,by decide⟩ (by decide)
  have hpr := intersection_on_left (L 60) (L r) hdr
  have hpp := intersection_on_right (L 0) (L 60) hdp
  have hlast : L 60=graphLine rightSlope (tan (29*π/60)) := last_line epsilon
  have hpr' : affineEval (graphLine rightSlope (tan (29*π/60))) (intersection (L 60) (L r))=0 := by
    rw [← hlast]
    exact hpr
  have hpp' : affineEval (graphLine rightSlope (tan (29*π/60))) (intersection (L 0) (L 60))=0 := by
    rw [← hlast]
    exact hpp
  have hdir : 0<w.a+w.b*(rightSlope:ℝ) := by
    dsimp [w,normalLine]
    norm_num [rightSlope]
  have hh := graph_projection_order rightSlope (tan (29*π/60)) w _ _ hpr' hpp' hdir hle
  simpa only [L,last_intersection,Prod.fst] using hh

theorem simple_lower_bound (epsilon : ℝ) (he : 0<epsilon) (hu : epsilon≤(1/100000000)) :
    SimpleLowerBound 61 1190 := by
  exact ⟨arrangement epsilon,no_parallel epsilon,no_concurrent epsilon he hu,
    triangles,increasing_nodup 61 triangles ordered,all_triangles epsilon he hu,by decide⟩

theorem exterior_lower_bound (epsilon : ℝ) (he : 0<epsilon) (hu : epsilon≤(1/100000000)) :
    SimpleLowerBound 62 1219 := by
  let L := arrangement epsilon
  let w := normalLine 1 (-8000441397/4000000000)
  have hw : Admissible 61 L w := admissible_sound 61 lineAt 1 (-8000441397/4000000000) (parameters epsilon) admissible_check
  have h := Exterior.extension 61 1190 L triangles visible w (safeHeight 61 L w)
    (no_parallel epsilon) (no_concurrent epsilon he hu)
    (increasing_nodup 61 triangles ordered) (all_triangles epsilon he hu) (by decide)
    (by decide +kernel) (all_visible epsilon he hu) hw (safeHeight_beyond 61 L w)
  simpa [visible] using h

theorem arbitrarily_small (eta : ℝ) (heta : 0<eta) :
    ∃ epsilon : ℝ, 0<epsilon ∧ epsilon<eta ∧ epsilon≤(1/100000000) ∧
      NoConcurrent 61 (arrangement epsilon) ∧
      (∀ t∈triangles, TrianglePredicate 61 (arrangement epsilon) t) ∧
      (∀ t∈visible, VisiblePair 61 (arrangement epsilon) (normalLine 1 (-8000441397/4000000000)) t) := by
  let epsilon := min (eta/2) ((1/100000000):ℝ)
  have he : 0<epsilon := lt_min (by linarith) (by norm_num)
  have hu : epsilon≤(1/100000000) := min_le_right _ _
  have hl : epsilon<eta := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  exact ⟨epsilon,he,hl,hu,no_concurrent epsilon he hu,all_triangles epsilon he hu,all_visible epsilon he hu⟩

#print axioms simple_lower_bound
#print axioms exterior_lower_bound
#print axioms arbitrarily_small
#print axioms rightmost_last
end Kobon.OpenMathConstructionPareto61



