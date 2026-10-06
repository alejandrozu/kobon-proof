import Kobon.BBLSeed49Normalized
import Kobon.BBLSeed49Exterior
import Kobon.BBLVisibleSeed
import Kobon.BBLVisibleReindex

/-! The sorted 49-line seed retains all boundary data needed for iteration. -/
namespace Kobon.BBLSeed49Visible
open Real Parametric Exterior HybridBoundary BBLExtrema BBLAnalytic
  BBLGridCuts BBLCrossingCoordinates BBLRealizedPencil BBLSeed49Normalized
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def normal : Line ℝ := normalLine 1 (-2)

theorem slope_right : slopes 47=(BBLSeed49Exterior.rightSlope : ℝ) := by
  norm_num [slopes,BBLSeed49.lineAt,BBLSeed49.lines,BBLSeed49Exterior.rightSlope]

theorem intercept_right (ε : ℝ) : oldIntercept 12 ε 47=tan (23*π/48) := by
  norm_num [oldIntercept,cut,rightAngle,alpha]
  congr 1
  ring

theorem right_boundary (ε : ℝ) (he : 0<ε) (hu : ε≤1/100)
    (i : Fin 49) (hi : i.val≠48) :
    (intersection (oldArrangement 12 ε slopes 48) (oldArrangement 12 ε slopes i)).1
      ≤oldIntercept 12 ε 47 := by
  rw [intercept_right,← graph_identity ε 48 (by decide),← graph_identity ε i i.isLt]
  exact BBLSeed49Exterior.rightmost_last ε he hu i hi

theorem admissible (ε : ℝ) : Admissible 49 (oldArrangement 12 ε slopes) normal := by
  apply BBLVisibleReindex.admissible_congr 49 _ _ normal (graph_identity ε)
  exact admissible_sound 49 BBLSeed49.lineAt 1 (-2) (BBLSeed49.parameters ε)
    BBLSeed49Exterior.admissible_check

theorem compatible (ε : ℝ) (he : 0<ε) (hu : ε≤1/100) :
    BBLVisibleSeed.Compatible 12 767 24 ε normal := by
  obtain ⟨s,hs⟩ := seed_with_slopes ε he hu
  refine ⟨{ toSeed := s
            visible := BBLSeed49Exterior.visible
            visible_nodup := BBLSeed49Exterior.visible_count.2
            visible_valid := ?_
            visible_count := ?_
            admissible := ?_
            right_positive := ?_
            right_direction := ?_
            right_boundary := ?_ }⟩
  · intro t htm
    rw [hs]
    exact BBLVisibleReindex.visible_congr 49 _ _ normal (graph_identity ε) t
      (BBLSeed49Exterior.all_visible ε he hu t htm)
  · exact le_of_eq BBLSeed49Exterior.visible_count.1.symm
  · rw [hs]
    exact admissible ε
  · rw [hs]
    norm_num only
    rw [slope_right]
    exact BBLSeed49Exterior.right_slope_positive
  · rw [hs]
    norm_num only
    rw [slope_right]
    norm_num [normal,normalLine,BBLSeed49Exterior.rightSlope]
  · intro i hi
    rw [hs]
    exact right_boundary ε he hu i hi

#print axioms compatible
end Kobon.BBLSeed49Visible
