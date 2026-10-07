import Kobon.OpenMathConstructionPareto61Normalized
import Kobon.BBLVisibleSeed
import Kobon.BBLVisibleReindex
namespace Kobon.OpenMathConstructionPareto61Visible
open Real Parametric Exterior HybridBoundary BBLExtrema BBLAnalytic
  BBLGridCuts BBLCrossingCoordinates BBLRealizedPencil OpenMathConstructionPareto61Normalized
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def normal : Line ℝ := normalLine 1 (-8000441397/4000000000)

theorem slope_right : slopes 59=(OpenMathConstructionPareto61.rightSlope : ℝ) := by
  norm_num [slopes,OpenMathConstructionPareto61.lineAt,OpenMathConstructionPareto61.lines,OpenMathConstructionPareto61Fast.lineFactor,OpenMathConstructionPareto61Fast.intLineAt,OpenMathConstructionPareto61Fast.intLines,OpenMathIntegerBoxes.castLine,OpenMathIntegerBoxes.castForm,OpenMathConstructionRescale.rescale,Parametric.scale,
    OpenMathConstructionPareto61.rightSlope]

theorem intercept_right (ε : ℝ) : oldIntercept 15 ε 59=tan (29*π/60) := by
  norm_num [oldIntercept,cut,rightAngle,alpha]
  congr 1
  ring

theorem right_boundary (ε : ℝ) (he : 0<ε) (hu : ε≤(1/100000000))
    (i : Fin 61) (hi : i.val≠60) :
    (intersection (oldArrangement 15 ε slopes 60) (oldArrangement 15 ε slopes i)).1
      ≤oldIntercept 15 ε 59 := by
  rw [intercept_right,← graph_identity ε 60 (by decide),← graph_identity ε i i.isLt]
  exact OpenMathConstructionPareto61.rightmost_last ε he hu i hi

theorem admissible (ε : ℝ) : Admissible 61 (oldArrangement 15 ε slopes) normal := by
  have hw : Admissible 61 (OpenMathConstructionPareto61.arrangement ε) normal :=
    admissible_sound 61 OpenMathConstructionPareto61.lineAt 1 (-8000441397/4000000000)
      (OpenMathConstructionPareto61.parameters ε) OpenMathConstructionPareto61.admissible_check
  exact BBLVisibleReindex.admissible_congr 61 _ _ normal (graph_identity ε) hw

theorem compatible (ε : ℝ) (he : 0<ε) (hu : ε≤(1/100000000)) :
    BBLVisibleSeed.Compatible 15 1190 29 ε normal := by
  obtain ⟨s,hs⟩ := seed_with_slopes ε he hu
  refine ⟨{ toSeed := s
            visible := OpenMathConstructionPareto61.visible
            visible_nodup := OpenMathConstructionPareto61.visible_count.2
            visible_valid := ?_
            visible_count := ?_
            admissible := ?_
            right_positive := ?_
            right_direction := ?_
            right_boundary := ?_ }⟩
  · intro t ht
    rw [hs]
    exact BBLVisibleReindex.visible_congr 61 _ _ normal (graph_identity ε) _
      (OpenMathConstructionPareto61.all_visible ε he hu _ ht)
  · have h := OpenMathConstructionPareto61.visible_count.1
    omega
  · rw [hs]
    exact admissible ε
  · rw [hs]
    norm_num only
    rw [slope_right]
    exact OpenMathConstructionPareto61.right_slope_positive
  · rw [hs]
    norm_num only
    rw [slope_right]
    norm_num [normal,normalLine,OpenMathConstructionPareto61.rightSlope]
  · intro i hi
    rw [hs]
    exact right_boundary ε he hu i hi

#print axioms compatible
end Kobon.OpenMathConstructionPareto61Visible

