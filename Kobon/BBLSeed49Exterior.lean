import Kobon.BBLSeed49
import Kobon.BBLProjection
import Kobon.OpenMathConstructionBooleanMemo

namespace Kobon.BBLSeed49Exterior
open Real Parametric Exterior HybridBoundary BBLExtrema BBLSeed49
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def rightSlope : ℚ := 1/3
def visible : List Triple := [⟨0,48,49⟩,⟨1,33,49⟩,⟨3,31,49⟩,⟨4,14,49⟩,⟨5,29,49⟩,⟨6,22,49⟩,⟨7,27,49⟩,⟨8,16,49⟩,⟨9,25,49⟩,⟨10,18,49⟩,⟨11,23,49⟩,⟨12,20,49⟩,⟨13,21,49⟩,⟨15,19,49⟩,⟨17,47,49⟩,⟨24,26,49⟩,⟨28,43,49⟩,⟨30,37,49⟩,⟨32,39,49⟩,⟨34,41,49⟩,⟨35,45,49⟩,⟨36,46,49⟩,⟨38,44,49⟩,⟨40,42,49⟩]

theorem admissible_check : AdmissibleCheck 49 lineAt 1 (-2) := by
  apply OpenMathConstructionBoolean.admissible_sound
  native_decide
theorem visible_checks :
    visible.all (fun t => decide (VisibleCheck 49 lo hi lineAt 1 (-2) t))=true := by
  apply OpenMathConstructionBooleanMemo.visibles_sound
  native_decide
theorem all_visible (epsilon : ℝ) (he : 0<epsilon) (hu : epsilon≤1/100)
    (t : Triple) (ht : t∈visible) :
    VisiblePair 49 (arrangement epsilon) (normalLine 1 (-2)) t := by
  have hc := visible_checks
  simp only [List.all_eq_true,decide_eq_true_eq] at hc
  exact visible_sound 49 lo hi lineAt 1 (-2) (parameters epsilon)
    (parameters_in_box epsilon he hu) directions admissible_check t (hc t ht)

theorem visible_count : visible.length=24 ∧ visible.Nodup := by decide +kernel

theorem zero_line (epsilon : ℝ) : arrangement epsilon 0=graphLine 0 0 := by
  norm_num [arrangement,toLine,lineAt,lines,graphLine,evaluate,Fin.sum_univ_succ]

theorem last_line (epsilon : ℝ) :
    arrangement epsilon 48=graphLine rightSlope (tan (23*π/48)) := by
  norm_num [arrangement,toLine,lineAt,lines,graphLine,evaluate,Fin.sum_univ_succ,
    rightSlope,parameters]

theorem right_slope_positive : (0:ℝ)<rightSlope := by norm_num [rightSlope]
theorem right_slope_small : (rightSlope:ℝ)<1/2 := by norm_num [rightSlope]

theorem last_intersection (epsilon : ℝ) :
    intersection (arrangement epsilon 0) (arrangement epsilon 48)=(tan (23*π/48),0) := by
  rw [zero_line,last_line]
  have hm : (rightSlope:ℝ) ≠ 0 := ne_of_gt right_slope_positive
  simp [intersection,vertex,graphLine,det,hm]

theorem rightmost_last (epsilon : ℝ) (he : 0<epsilon) (hu : epsilon≤1/100)
    (r : Fin 49) (hr : r.val ≠ 48) :
    (intersection (arrangement epsilon 48) (arrangement epsilon r)).1≤tan (23*π/48) := by
  let L := arrangement epsilon
  let w := normalLine 1 (-2)
  have hp := no_parallel epsilon
  have hw : Admissible 49 L w := admissible_sound 49 lineAt 1 (-2) (parameters epsilon) admissible_check
  have hv : VisiblePair 49 L w ⟨0,48,49⟩ := all_visible epsilon he hu _ (by simp [visible])
  have hle := visible_extremal_right 49 L w hp hw ⟨0,48,49⟩ hv r hr
  have hdr : det (L 48) (L r) ≠ 0 := det_ne_of_ne 49 L hp ⟨48,by decide⟩ r (by
    intro hh
    exact hr (congrArg Fin.val hh).symm)
  have hdp : det (L 0) (L 48) ≠ 0 := hp ⟨0,by decide⟩ ⟨48,by decide⟩ (by decide)
  have hpr := intersection_on_left (L 48) (L r) hdr
  have hpp := intersection_on_right (L 0) (L 48) hdp
  have hlast : L 48=graphLine rightSlope (tan (23*π/48)) := last_line epsilon
  have hpr' : affineEval (graphLine rightSlope (tan (23*π/48))) (intersection (L 48) (L r))=0 := by
    rw [← hlast]
    exact hpr
  have hpp' : affineEval (graphLine rightSlope (tan (23*π/48))) (intersection (L 0) (L 48))=0 := by
    rw [← hlast]
    exact hpp
  have hdir : 0<w.a+w.b*(rightSlope:ℝ) := by
    dsimp [w,normalLine]
    norm_num [rightSlope]
  have hh := graph_projection_order rightSlope (tan (23*π/48)) w _ _ hpr' hpp' hdir hle
  simpa only [L,last_intersection,Prod.fst] using hh

theorem exterior_lower_bound (epsilon : ℝ) (he : 0<epsilon) (hu : epsilon≤1/100) :
    SimpleLowerBound 50 791 := by
  have h := Exterior.extension 49 767 (arrangement epsilon) triangles visible
    (normalLine 1 (-2)) (safeHeight 49 (arrangement epsilon) (normalLine 1 (-2)))
    (no_parallel epsilon) (no_concurrent epsilon he hu)
    (increasing_nodup 49 triangles ordered) (all_triangles epsilon he hu) (by decide)
    visible_count.2 (all_visible epsilon he hu)
    (admissible_sound 49 lineAt 1 (-2) (parameters epsilon) admissible_check)
    (safeHeight_beyond 49 (arrangement epsilon) (normalLine 1 (-2)))
  simpa [visible] using h

#print axioms all_visible
#print axioms rightmost_last
#print axioms exterior_lower_bound
end Kobon.BBLSeed49Exterior
