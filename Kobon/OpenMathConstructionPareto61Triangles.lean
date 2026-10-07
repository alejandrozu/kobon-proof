import Kobon.OpenMathConstructionPareto61Simple
import Kobon.OpenMathConstructionPareto61IntegerFastTriangles
namespace Kobon.OpenMathConstructionPareto61
open Parametric HybridBoundary
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

theorem triangle_checks : triangles.all (fun t => decide (TriangleCheck 61 lo hi lineAt t))=true := by
  apply List.all_eq_true.mpr
  intro t ht
  apply decide_eq_true
  exact OpenMathConstructionPareto61Fast.intTriangle_transfer t
    (OpenMathIntegerBoxes.triangle_sound OpenMathConstructionPareto61Fast.gridDen
      (by norm_num [OpenMathConstructionPareto61Fast.gridDen]) 61
      OpenMathConstructionPareto61Fast.loInt OpenMathConstructionPareto61Fast.hiInt
      OpenMathConstructionPareto61Fast.intLineAt t
      ((List.all_eq_true.mp OpenMathConstructionPareto61Fast.int_triangles_bool) t ht))
#print axioms triangle_checks
end Kobon.OpenMathConstructionPareto61
