import Kobon.TamuraSeed33Normalized
import Kobon.BBLVisibleSeed
import Kobon.BBLVisibleReindex

/-! The verified 33-line seed also supplies the full recursive boundary data.
The visible-pair list is transported exactly through the sorted labeling. -/
namespace Kobon.TamuraSeed33Visible
open Real Parametric Exterior HybridBoundary BBLExtrema BBLAnalytic
  BBLGridCuts BBLCrossingCoordinates BBLRealizedPencil TamuraSeed33Normalized
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def normal : Line ℝ := normalLine 10 (-13)

theorem slope_right : slopes 31=(TamuraSeed33.rightSlope : ℝ) := by
  norm_num [slopes,perm,TamuraSeed33.lineAt,TamuraSeed33.lines,TamuraSeed33.rightSlope]

theorem intercept_right (ε : ℝ) : oldIntercept 8 ε 31=tan (15*π/32) := by
  norm_num [oldIntercept,cut,rightAngle,alpha]
  congr 1
  ring

theorem right_boundary (ε : ℝ) (he : 0<ε) (hu : ε≤1/100000)
    (i : Fin 33) (hi : i.val≠32) :
    (intersection (oldArrangement 8 ε slopes 32) (oldArrangement 8 ε slopes i)).1
      ≤oldIntercept 8 ε 31 := by
  rw [intercept_right,← graph_identity ε 32 (by decide),← graph_identity ε i i.isLt]
  have hp : perm i≠32 := by
    intro h
    have hh := perm_injective i ⟨32,by decide⟩ (by
      simpa only [show perm (⟨32,by decide⟩ : Fin 33)=32 by decide +kernel] using h)
    exact hi (congrArg Fin.val hh)
  simpa only [show perm 32=32 by decide +kernel] using
    TamuraSeed33.rightmost_last ε he hu ⟨perm i,perm_bound i⟩ hp

theorem admissible (ε : ℝ) : Admissible 33 (oldArrangement 8 ε slopes) normal := by
  have hw : Admissible 33 (TamuraSeed33.arrangement ε) normal :=
    admissible_sound 33 TamuraSeed33.lineAt 10 (-13) (TamuraSeed33.parameters ε)
      TamuraSeed33.admissible_check
  apply BBLVisibleReindex.admissible_congr 33 _ _ normal (graph_identity ε)
  exact BBLVisibleReindex.admissible_pullback 33 33 _ normal perm perm_bound hw

theorem compatible (ε : ℝ) (he : 0<ε) (hu : ε≤1/100000) :
    BBLVisibleSeed.Compatible 8 341 16 ε normal := by
  obtain ⟨s,hs⟩ := seed_with_slopes ε he hu
  obtain ⟨vs,hn,hv,hc⟩ := BBLVisibleReindex.transport_list_of_injective 33
    (TamuraSeed33.arrangement ε) normal perm perm_bound perm_injective
    TamuraSeed33.visible TamuraSeed33.visible_count.2 (TamuraSeed33.all_visible ε he hu)
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
    exact BBLVisibleReindex.visible_congr 33 _ _ normal (graph_identity ε) t (hv t htm)
  · have hlen := TamuraSeed33.visible_count.1
    omega
  · rw [hs]
    exact admissible ε
  · rw [hs]
    norm_num only
    rw [slope_right]
    exact TamuraSeed33.right_slope_positive
  · rw [hs]
    norm_num only
    rw [slope_right]
    norm_num [normal,normalLine,TamuraSeed33.rightSlope]
  · intro i hi
    rw [hs]
    exact right_boundary ε he hu i hi

#print axioms compatible
end Kobon.TamuraSeed33Visible
