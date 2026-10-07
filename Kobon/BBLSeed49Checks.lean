import Kobon.BBLSeed49Data
import Kobon.OpenMathConstructionBooleanMemo

/-! Finite exact interval checks for the uniform 49-line seed.  Boolean
evaluation is separated from the ordinary soundness proofs and its native
evaluation dependencies are printed explicitly. -/
namespace Kobon.BBLSeed49Checks
open Parametric BBLSeed49
set_option maxHeartbeats 0
set_option maxRecDepth 4096
set_option trace.profiler true

private theorem directions_bool :
    OpenMathConstructionBoolean.directionsBool 49 lineAt = true := by native_decide

theorem directions : DirectionCheck 49 lineAt :=
  OpenMathConstructionBoolean.directions_sound 49 lineAt directions_bool
#eval do IO.println "seed49: directions checked"; (← IO.getStdout).flush

private theorem simple_bool :
    OpenMathConstructionBooleanMemo.simpleBool 49 lo hi 23 lineAt = true := by native_decide

theorem simple : SimpleCheck 49 lo hi 23 lineAt :=
  OpenMathConstructionBooleanMemo.simple_sound 49 lo hi 23 lineAt simple_bool
#eval do IO.println "seed49: simplicity checked"; (← IO.getStdout).flush

private theorem triangle_bool :
    OpenMathConstructionBooleanMemo.trianglesBool 49 lo hi lineAt triangles = true := by
  native_decide

theorem triangle_checks :
    triangles.all (fun t => decide (TriangleCheck 49 lo hi lineAt t)) = true :=
  OpenMathConstructionBooleanMemo.triangles_sound 49 lo hi lineAt triangles triangle_bool
#eval do IO.println "seed49: all 767 triangles checked"; (← IO.getStdout).flush

def orderedBool (n : Nat) (ts : List Triple) : Bool := decide (Increasing n ts)

theorem ordered : Increasing 49 triangles := by
  have h : orderedBool 49 triangles = true := by native_decide
  exact of_decide_eq_true h

def subsetBool (xs ys : List Triple) : Bool :=
  xs.all (fun t => decide (t ∈ ys))

theorem distinguished_subset : ∀ t∈distinguished, t∈triangles := by
  have h : subsetBool distinguished triangles = true := by native_decide
  simpa only [subsetBool,List.all_eq_true,decide_eq_true_eq] using h

#print axioms directions
#print axioms simple
#print axioms triangle_checks
#print axioms ordered
#print axioms distinguished_subset
end Kobon.BBLSeed49Checks
