import Kobon.OpenMathConstructionSeed61Normalized
import Kobon.BBLVisibleSeed
import Kobon.BBLVisibleReindex
namespace Kobon.OpenMathConstructionSeed61Visible
open Real Parametric Exterior HybridBoundary BBLExtrema BBLAnalytic
  BBLGridCuts BBLCrossingCoordinates BBLRealizedPencil OpenMathConstructionSeed61Normalized
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def normal : Line ℝ := normalLine 1 (-20025598529/10000000000)

theorem slope_right : slopes 59=(OpenMathConstructionSeed61.rightSlope : ℝ) := by
  norm_num [slopes,OpenMathConstructionSeed61.lineAt,OpenMathConstructionSeed61.lines,OpenMathConstructionSeed61Fast.lineFactor,OpenMathConstructionSeed61Fast.intLineAt,OpenMathConstructionSeed61Fast.intLines,OpenMathIntegerBoxes.castLine,OpenMathIntegerBoxes.castForm,OpenMathConstructionRescale.rescale,Parametric.scale,
    OpenMathConstructionSeed61.rightSlope]

theorem intercept_right (ε : ℝ) : oldIntercept 15 ε 59=tan (29*π/60) := by
  norm_num [oldIntercept,cut,rightAngle,alpha]
  congr 1
  ring

theorem right_boundary (ε : ℝ) (he : 0<ε) (hu : ε≤(1/100000000))
    (i : Fin 61) (hi : i.val≠60) :
    (intersection (oldArrangement 15 ε slopes 60) (oldArrangement 15 ε slopes i)).1
      ≤oldIntercept 15 ε 59 := by
  rw [intercept_right,← graph_identity ε 60 (by decide),← graph_identity ε i i.isLt]
  exact OpenMathConstructionSeed61.rightmost_last ε he hu i hi

theorem admissible (ε : ℝ) : Admissible 61 (oldArrangement 15 ε slopes) normal := by
  have hw : Admissible 61 (OpenMathConstructionSeed61.arrangement ε) normal :=
    admissible_sound 61 OpenMathConstructionSeed61.lineAt 1 (-20025598529/10000000000)
      (OpenMathConstructionSeed61.parameters ε) OpenMathConstructionSeed61.admissible_check
  exact BBLVisibleReindex.admissible_congr 61 _ _ normal (graph_identity ε) hw

theorem compatible (ε : ℝ) (he : 0<ε) (hu : ε≤(1/100000000)) :
    BBLVisibleSeed.Compatible 15 1190 28 ε normal := by
  obtain ⟨s,hs⟩ := seed_with_slopes ε he hu
  refine ⟨{ toSeed := s
            visible := OpenMathConstructionSeed61.visible
            visible_nodup := OpenMathConstructionSeed61.visible_count.2
            visible_valid := ?_
            visible_count := ?_
            admissible := ?_
            right_positive := ?_
            right_direction := ?_
            right_boundary := ?_ }⟩
  · intro t ht
    rw [hs]
    exact BBLVisibleReindex.visible_congr 61 _ _ normal (graph_identity ε) _
      (OpenMathConstructionSeed61.all_visible ε he hu _ ht)
  · have h := OpenMathConstructionSeed61.visible_count.1
    omega
  · rw [hs]
    exact admissible ε
  · rw [hs]
    norm_num only
    rw [slope_right]
    exact OpenMathConstructionSeed61.right_slope_positive
  · rw [hs]
    norm_num only
    rw [slope_right]
    norm_num [normal,normalLine,OpenMathConstructionSeed61.rightSlope]
  · intro i hi
    rw [hs]
    exact right_boundary ε he hu i hi

#print axioms compatible
end Kobon.OpenMathConstructionSeed61Visible

