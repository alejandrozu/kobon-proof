import Kobon.OpenMathConstructionSeed61Simple
import Kobon.OpenMathConstructionSeed61IntegerFastTriangles
namespace Kobon.OpenMathConstructionSeed61
open Parametric HybridBoundary
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

theorem triangle_checks : triangles.all (fun t => decide (TriangleCheck 61 lo hi lineAt t))=true := by
  apply List.all_eq_true.mpr
  intro t ht
  apply decide_eq_true
  exact OpenMathConstructionSeed61Fast.intTriangle_transfer t
    (OpenMathIntegerBoxes.triangle_sound OpenMathConstructionSeed61Fast.gridDen
      (by norm_num [OpenMathConstructionSeed61Fast.gridDen]) 61
      OpenMathConstructionSeed61Fast.loInt OpenMathConstructionSeed61Fast.hiInt
      OpenMathConstructionSeed61Fast.intLineAt t
      ((List.all_eq_true.mp OpenMathConstructionSeed61Fast.int_triangles_bool) t ht))
#print axioms triangle_checks
end Kobon.OpenMathConstructionSeed61
