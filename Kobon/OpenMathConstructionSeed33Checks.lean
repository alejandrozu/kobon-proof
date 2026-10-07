import Kobon.OpenMathConstructionSeed33Simple
namespace Kobon.OpenMathConstructionSeed33
open Parametric HybridBoundary
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

theorem triangles_bool :
    OpenMathConstructionBooleanMemo.trianglesBool 33 lo hi lineAt triangles=true := by native_decide

theorem triangle_checks :
    triangles.all (fun t => decide (TriangleCheck 33 lo hi lineAt t))=true :=
  OpenMathConstructionBooleanMemo.triangles_sound 33 lo hi lineAt triangles triangles_bool

theorem distinguished_subset_bool :
    distinguished.all (fun t => decide (t∈triangles))=true := by native_decide

theorem distinguished_checks :
    distinguished.all (fun t => decide (TriangleCheck 33 lo hi lineAt t))=true := by
  apply List.all_eq_true.mpr
  intro t ht
  exact (List.all_eq_true.mp triangle_checks) t
    (of_decide_eq_true ((List.all_eq_true.mp distinguished_subset_bool) t ht))

theorem ordered : Increasing 33 triangles := by decide +kernel

theorem admissible_bool :
    OpenMathConstructionBoolean.admissibleBool 33 lineAt 10 (-13)=true := by native_decide

theorem admissible_check : AdmissibleCheck 33 lineAt 10 (-13) :=
  OpenMathConstructionBoolean.admissible_sound 33 lineAt 10 (-13) admissible_bool

theorem visible_bool :
    OpenMathConstructionBooleanMemo.visiblesBool 33 lo hi lineAt 10 (-13) visible=true := by native_decide

theorem visible_checks :
    visible.all (fun t => decide (VisibleCheck 33 lo hi lineAt 10 (-13) t))=true :=
  OpenMathConstructionBooleanMemo.visibles_sound 33 lo hi lineAt 10 (-13) visible visible_bool

#print axioms triangle_checks
#print axioms visible_checks
end Kobon.OpenMathConstructionSeed33
