import Kobon.OpenMathConstructionPareto61Triangles
import Kobon.OpenMathConstructionRescale
import Kobon.OpenMathSparseBoxes
namespace Kobon.OpenMathConstructionPareto61
open Parametric HybridBoundary
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false
set_option trace.profiler false

theorem distinguished_subset_bool : distinguished.all (fun t => decide (t∈triangles))=true := by native_decide

theorem distinguished_checks : distinguished.all (fun t => decide (TriangleCheck 61 lo hi lineAt t))=true := by
  apply List.all_eq_true.mpr
  intro t ht
  exact (List.all_eq_true.mp triangle_checks) t
    (of_decide_eq_true ((List.all_eq_true.mp distinguished_subset_bool) t ht))

def orderedBool (n : Nat) (ts : List Triple) : Bool := decide (Increasing n ts)

theorem ordered_bool : orderedBool 61 triangles=true := by native_decide

theorem ordered : Increasing 61 triangles := of_decide_eq_true ordered_bool

theorem admissible_bool : OpenMathConstructionBoolean.admissibleBool 61 lineAt 1 (-8000441397/4000000000)=true := by native_decide

theorem admissible_check : AdmissibleCheck 61 lineAt 1 (-8000441397/4000000000) :=
  OpenMathConstructionBoolean.admissible_sound 61 lineAt 1 (-8000441397/4000000000) admissible_bool

theorem visible_bool : OpenMathConstructionRescale.clearedVisiblesBool 61 lo hi lineAt 1 (-8000441397/4000000000) visible=true := by native_decide

theorem visible_checks : visible.all (fun t => decide (VisibleCheck 61 lo hi lineAt 1 (-8000441397/4000000000) t))=true :=
  OpenMathConstructionRescale.clearedVisibles_sound 61 lo hi lineAt 1 (-8000441397/4000000000) visible visible_bool

#print axioms simple
#print axioms triangle_checks
#print axioms visible_checks
end Kobon.OpenMathConstructionPareto61

