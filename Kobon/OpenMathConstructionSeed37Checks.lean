import Kobon.OpenMathConstructionSeed37Triangles
import Kobon.OpenMathConstructionRescale
import Kobon.OpenMathSparseBoxes
namespace Kobon.OpenMathConstructionSeed37
open Parametric HybridBoundary
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false
set_option trace.profiler false

theorem distinguished_subset_bool : distinguished.all (fun t => decide (t∈triangles))=true := by native_decide

theorem distinguished_checks : distinguished.all (fun t => decide (TriangleCheck 37 lo hi lineAt t))=true := by
  apply List.all_eq_true.mpr
  intro t ht
  exact (List.all_eq_true.mp triangle_checks) t
    (of_decide_eq_true ((List.all_eq_true.mp distinguished_subset_bool) t ht))

def orderedBool (n : Nat) (ts : List Triple) : Bool := decide (Increasing n ts)

theorem ordered_bool : orderedBool 37 triangles=true := by native_decide

theorem ordered : Increasing 37 triangles := of_decide_eq_true ordered_bool

#print axioms simple
#print axioms triangle_checks
end Kobon.OpenMathConstructionSeed37
