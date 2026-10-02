import Kobon.BBLSeed21Normalized
import Kobon.BBLVisibleSeed
import Kobon.BBLVisibleReindex

/-! The verified 21-line seed also supplies the full recursive boundary data.
The visible-pair list is transported exactly through the sorted labeling. -/
namespace Kobon.BBLSeed21Visible
open Real Parametric Exterior HybridBoundary BBLExtrema BBLAnalytic
  BBLGridCuts BBLCrossingCoordinates BBLRealizedPencil BBLSeed21Normalized
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def normal : Line ℝ := normalLine 10 (-13)

theorem slope_right : slopes 19=(BBLSeed21.rightSlope : ℝ) := by
  norm_num [slopes,perm,BBLSeed21.lineAt,BBLSeed21.lines,BBLSeed21.rightSlope]

theorem intercept_right (ε : ℝ) : oldIntercept 5 ε 19=tan (9*π/20) := by
  norm_num [oldIntercept,cut,rightAngle,alpha]
  congr 1
  ring

theorem right_boundary (ε : ℝ) (he : 0<ε) (hu : ε≤1/100000)
    (i : Fin 21) (hi : i.val≠20) :
    (intersection (oldArrangement 5 ε slopes 20) (oldArrangement 5 ε slopes i)).1
      ≤oldIntercept 5 ε 19 := by
  rw [intercept_right,← graph_identity ε 20 (by decide),← graph_identity ε i i.isLt]
  have hp : perm i≠20 := by
    intro h
    have hh := perm_injective i ⟨20,by decide⟩ (by
      simpa only [show perm (⟨20,by decide⟩ : Fin 21)=20 by decide +kernel] using h)
    exact hi (congrArg Fin.val hh)
  simpa only [show perm 20=20 by decide +kernel] using
    BBLSeed21.rightmost_last ε he hu ⟨perm i,perm_bound i⟩ hp

theorem admissible (ε : ℝ) : Admissible 21 (oldArrangement 5 ε slopes) normal := by
  have hw : Admissible 21 (BBLSeed21.arrangement ε) normal :=
    admissible_sound 21 BBLSeed21.lineAt 10 (-13) (BBLSeed21.parameters ε)
      BBLSeed21.admissible_check
  apply BBLVisibleReindex.admissible_congr 21 _ _ normal (graph_identity ε)
  exact BBLVisibleReindex.admissible_pullback 21 21 _ normal perm perm_bound hw

theorem compatible (ε : ℝ) (he : 0<ε) (hu : ε≤1/100000) :
    BBLVisibleSeed.Compatible 5 132 10 ε normal := by
  obtain ⟨s,hs⟩ := seed_with_slopes ε he hu
  obtain ⟨vs,hn,hv,hc⟩ := BBLVisibleReindex.transport_list_of_injective 21
    (BBLSeed21.arrangement ε) normal perm perm_bound perm_injective
    BBLSeed21.visible BBLSeed21.visible_count.2 (BBLSeed21.all_visible ε he hu)
  refine ⟨{ toSeed := s
            visible := vs
            visible_nodup := hn
            visible_valid := ?_
            visible_count := ?_
            admissible := ?_
            right_positive := ?_
            right_direction := ?_
            right_boundary := ?_ }⟩
  · intro t htm
    rw [hs]
    exact BBLVisibleReindex.visible_congr 21 _ _ normal (graph_identity ε) t (hv t htm)
  · have hlen := BBLSeed21.visible_count.1
    omega
  · rw [hs]
    exact admissible ε
  · rw [hs]
    norm_num only
    rw [slope_right]
    exact BBLSeed21.right_slope_positive
  · rw [hs]
    norm_num only
    rw [slope_right]
    norm_num [normal,normalLine,BBLSeed21.rightSlope]
  · intro i hi
    rw [hs]
    exact right_boundary ε he hu i hi

#print axioms compatible
end Kobon.BBLSeed21Visible
