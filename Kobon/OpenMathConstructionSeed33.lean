import Kobon.OpenMathConstructionSeed33Checks
/-! Actual uniform classical 33-line seed, checked through executable Boolean reflection.
The source coordinates are the existing Forge--Ramirez Alfonsin construction.
The actual tangent bounds and geometric bridges are ordinary kernel proofs;
finite Bool computations retain the explicitly audited native-evaluation trust. -/
namespace Kobon.OpenMathConstructionSeed33
open Parametric Exterior HybridBoundary BBLExtrema Real
set_option maxRecDepth 100000
set_option maxHeartbeats 0

noncomputable def parameters (epsilon : ℝ) : Fin 16 → ℝ :=
  ![tan (1*π/32),tan (2*π/32),tan (3*π/32),tan (4*π/32),tan (5*π/32),tan (6*π/32),tan (7*π/32),tan (8*π/32),tan (9*π/32),tan (10*π/32),tan (11*π/32),tan (12*π/32),tan (13*π/32),tan (14*π/32),tan (15*π/32),epsilon]

noncomputable def arrangement (epsilon : ℝ) (i : Nat) : Line ℝ :=
  toLine (lineAt i) (parameters epsilon)

theorem parameters_in_box (epsilon : ℝ) (he : 0<epsilon) (hu : epsilon≤1/100000) :
    InBox lo hi (parameters epsilon) := by
  intro i
  fin_cases i
  · have h := TamuraTangentBounds.tan_32_1_bounds
    try simp only [one_mul] at h
    norm_num [lo,hi,parameters]
    constructor <;> linarith [h.1,h.2]
  · have h := TamuraTangentBounds.tan_32_2_bounds
    try simp only [one_mul] at h
    norm_num [lo,hi,parameters]
    constructor <;> linarith [h.1,h.2]
  · have h := TamuraTangentBounds.tan_32_3_bounds
    try simp only [one_mul] at h
    norm_num [lo,hi,parameters]
    constructor <;> linarith [h.1,h.2]
  · have h := TamuraTangentBounds.tan_32_4_bounds
    try simp only [one_mul] at h
    norm_num [lo,hi,parameters]
    constructor <;> linarith [h.1,h.2]
  · have h := TamuraTangentBounds.tan_32_5_bounds
    try simp only [one_mul] at h
    norm_num [lo,hi,parameters]
    constructor <;> linarith [h.1,h.2]
  · have h := TamuraTangentBounds.tan_32_6_bounds
    try simp only [one_mul] at h
    norm_num [lo,hi,parameters]
    constructor <;> linarith [h.1,h.2]
  · have h := TamuraTangentBounds.tan_32_7_bounds
    try simp only [one_mul] at h
    norm_num [lo,hi,parameters]
    constructor <;> linarith [h.1,h.2]
  · have h := TamuraTangentBounds.tan_32_8_bounds
    try simp only [one_mul] at h
    norm_num [lo,hi,parameters]
    constructor <;> linarith [h.1,h.2]
  · have h := TamuraTangentBounds.tan_32_9_bounds
    try simp only [one_mul] at h
    norm_num [lo,hi,parameters]
    constructor <;> linarith [h.1,h.2]
  · have h := TamuraTangentBounds.tan_32_10_bounds
    try simp only [one_mul] at h
    norm_num [lo,hi,parameters]
    constructor <;> linarith [h.1,h.2]
  · have h := TamuraTangentBounds.tan_32_11_bounds
    try simp only [one_mul] at h
    norm_num [lo,hi,parameters]
    constructor <;> linarith [h.1,h.2]
  · have h := TamuraTangentBounds.tan_32_12_bounds
    try simp only [one_mul] at h
    norm_num [lo,hi,parameters]
    constructor <;> linarith [h.1,h.2]
  · have h := TamuraTangentBounds.tan_32_13_bounds
    try simp only [one_mul] at h
    norm_num [lo,hi,parameters]
    constructor <;> linarith [h.1,h.2]
  · have h := TamuraTangentBounds.tan_32_14_bounds
    try simp only [one_mul] at h
    norm_num [lo,hi,parameters]
    constructor <;> linarith [h.1,h.2]
  · have h := TamuraTangentBounds.tan_32_15_bounds
    try simp only [one_mul] at h
    norm_num [lo,hi,parameters]
    constructor <;> linarith [h.1,h.2]
  · simpa [lo,hi,parameters] using And.intro (le_of_lt he) hu

theorem no_parallel (epsilon : ℝ) : NoParallel 33 (arrangement epsilon) :=
  directions_sound 33 lineAt (parameters epsilon) directions

theorem no_concurrent (epsilon : ℝ) (he : 0<epsilon) (hu : epsilon≤1/100000) :
    NoConcurrent 33 (arrangement epsilon) := by
  exact simple_sound 33 lo hi 15 lineAt (parameters epsilon)
    (parameters_in_box epsilon he hu) (by simpa [parameters] using he) simple

theorem all_triangles (epsilon : ℝ) (he : 0<epsilon) (hu : epsilon≤1/100000)
    (t : Triple) (ht : t∈triangles) : TrianglePredicate 33 (arrangement epsilon) t := by
  have hc := triangle_checks
  simp only [List.all_eq_true,decide_eq_true_eq] at hc
  exact triangle_sound 33 lo hi 15 lineAt (parameters epsilon)
    (parameters_in_box epsilon he hu) (by simpa [parameters] using he) simple t (hc t ht)

theorem all_visible (epsilon : ℝ) (he : 0<epsilon) (hu : epsilon≤1/100000)
    (t : Triple) (ht : t∈visible) :
    VisiblePair 33 (arrangement epsilon) (normalLine 10 (-13)) t := by
  have hc := visible_checks
  simp only [List.all_eq_true,decide_eq_true_eq] at hc
  exact visible_sound 33 lo hi lineAt 10 (-13) (parameters epsilon)
    (parameters_in_box epsilon he hu) directions admissible_check t (hc t ht)

theorem all_distinguished (epsilon : ℝ) (he : 0<epsilon) (hu : epsilon≤1/100000)
    (t : Triple) (ht : t∈distinguished) : TrianglePredicate 33 (arrangement epsilon) t := by
  have hc := distinguished_checks
  simp only [List.all_eq_true,decide_eq_true_eq] at hc
  exact triangle_sound 33 lo hi 15 lineAt (parameters epsilon)
    (parameters_in_box epsilon he hu) (by simpa [parameters] using he) simple t (hc t ht)

theorem distinguished_count : distinguished.length=31 ∧ distinguished.Nodup := by decide +kernel
theorem visible_count : visible.length=16 ∧ visible.Nodup := by decide +kernel

theorem zero_line (epsilon : ℝ) : arrangement epsilon 0=graphLine 0 0 := by
  norm_num [arrangement,toLine,lineAt,lines,graphLine,evaluate,Fin.sum_univ_succ]

theorem last_line (epsilon : ℝ) :
    arrangement epsilon 32=graphLine rightSlope (tan (15*π/32)) := by
  norm_num [arrangement,toLine,lineAt,lines,graphLine,evaluate,Fin.sum_univ_succ,
    rightSlope,parameters]

theorem right_slope_positive : (0:ℝ)<rightSlope := by norm_num [rightSlope]
theorem right_slope_small : (rightSlope:ℝ)<10/13 := by norm_num [rightSlope]

theorem last_intersection (epsilon : ℝ) :
    intersection (arrangement epsilon 0) (arrangement epsilon 32)=(tan (15*π/32),0) := by
  rw [zero_line,last_line]
  have hm : (rightSlope:ℝ) ≠ 0 := ne_of_gt right_slope_positive
  simp [intersection,vertex,graphLine,det,hm]

theorem rightmost_last (epsilon : ℝ) (he : 0<epsilon) (hu : epsilon≤1/100000)
    (r : Fin 33) (hr : r.val ≠ 32) :
    (intersection (arrangement epsilon 32) (arrangement epsilon r)).1≤tan (15*π/32) := by
  let L := arrangement epsilon
  let w := normalLine 10 (-13)
  have hp := no_parallel epsilon
  have hw : Admissible 33 L w := admissible_sound 33 lineAt 10 (-13) (parameters epsilon) admissible_check
  have hv : VisiblePair 33 L w ⟨0,32,33⟩ := all_visible epsilon he hu _ (by simp [visible])
  have hle := visible_extremal_right 33 L w hp hw ⟨0,32,33⟩ hv r hr
  have hdr : det (L 32) (L r) ≠ 0 := det_ne_of_ne 33 L hp ⟨32,by decide⟩ r (by
    intro hh
    exact hr (congrArg Fin.val hh).symm)
  have hdp : det (L 0) (L 32) ≠ 0 := hp ⟨0,by decide⟩ ⟨32,by decide⟩ (by decide)
  have hpr := intersection_on_left (L 32) (L r) hdr
  have hpp := intersection_on_right (L 0) (L 32) hdp
  have hlast : L 32=graphLine rightSlope (tan (15*π/32)) := last_line epsilon
  have hpr' : affineEval (graphLine rightSlope (tan (15*π/32))) (intersection (L 32) (L r))=0 := by
    rw [← hlast]
    exact hpr
  have hpp' : affineEval (graphLine rightSlope (tan (15*π/32))) (intersection (L 0) (L 32))=0 := by
    rw [← hlast]
    exact hpp
  have hdir : 0<w.a+w.b*(rightSlope:ℝ) := by
    dsimp [w,normalLine]
    norm_num [rightSlope]
  have hh := graph_projection_order rightSlope (tan (15*π/32)) w _ _ hpr' hpp' hdir hle
  simpa only [L,last_intersection,Prod.fst] using hh

theorem simple_lower_bound (epsilon : ℝ) (he : 0<epsilon) (hu : epsilon≤1/100000) :
    SimpleLowerBound 33 341 := by
  exact ⟨arrangement epsilon,no_parallel epsilon,no_concurrent epsilon he hu,
    triangles,increasing_nodup 33 triangles ordered,all_triangles epsilon he hu,by decide⟩

theorem exterior_lower_bound (epsilon : ℝ) (he : 0<epsilon) (hu : epsilon≤1/100000) :
    SimpleLowerBound 34 357 := by
  let L := arrangement epsilon
  let w := normalLine 10 (-13)
  have hw : Admissible 33 L w := admissible_sound 33 lineAt 10 (-13) (parameters epsilon) admissible_check
  have h := Exterior.extension 33 341 L triangles visible w (safeHeight 33 L w)
    (no_parallel epsilon) (no_concurrent epsilon he hu)
    (increasing_nodup 33 triangles ordered) (all_triangles epsilon he hu) (by decide)
    (by decide +kernel) (all_visible epsilon he hu) hw (safeHeight_beyond 33 L w)
  simpa [visible] using h

theorem arbitrarily_small (eta : ℝ) (heta : 0<eta) :
    ∃ epsilon : ℝ, 0<epsilon ∧ epsilon<eta ∧ epsilon≤1/100000 ∧
      NoConcurrent 33 (arrangement epsilon) ∧
      (∀ t∈triangles, TrianglePredicate 33 (arrangement epsilon) t) ∧
      (∀ t∈visible, VisiblePair 33 (arrangement epsilon) (normalLine 10 (-13)) t) := by
  let epsilon := min (eta/2) (1/100000:ℝ)
  have he : 0<epsilon := lt_min (by linarith) (by norm_num)
  have hu : epsilon≤1/100000 := min_le_right _ _
  have hl : epsilon<eta := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  exact ⟨epsilon,he,hl,hu,no_concurrent epsilon he hu,all_triangles epsilon he hu,all_visible epsilon he hu⟩

#print axioms simple_lower_bound
#print axioms exterior_lower_bound
#print axioms arbitrarily_small
#print axioms rightmost_last
end Kobon.OpenMathConstructionSeed33
