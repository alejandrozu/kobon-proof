import Kobon.OpenMathConstructionSeed37Simple
import Kobon.OpenMathConstructionSeed37IntegerFastTriangles
namespace Kobon.OpenMathConstructionSeed37
open Parametric HybridBoundary
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

theorem triangle_checks : triangles.all (fun t => decide (TriangleCheck 37 lo hi lineAt t))=true := by
  apply List.all_eq_true.mpr
  intro t ht
  apply decide_eq_true
  exact OpenMathConstructionSeed37Fast.intTriangle_transfer t
    (OpenMathIntegerBoxes.triangle_sound OpenMathConstructionSeed37Fast.gridDen
      (by norm_num [OpenMathConstructionSeed37Fast.gridDen]) 37
      OpenMathConstructionSeed37Fast.loInt OpenMathConstructionSeed37Fast.hiInt
      OpenMathConstructionSeed37Fast.intLineAt t
      ((List.all_eq_true.mp OpenMathConstructionSeed37Fast.int_triangles_bool) t ht))
#print axioms triangle_checks
end Kobon.OpenMathConstructionSeed37
