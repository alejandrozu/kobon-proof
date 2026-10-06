import Kobon.OpenMathConstructionPareto61IntegerFastData
import Kobon.OpenMathConstructionPareto61IntegerFastSimple
namespace Kobon.OpenMathConstructionPareto61
open Parametric HybridBoundary
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

theorem directions_bool : OpenMathConstructionBoolean.directionsBool 61 lineAt=true := by native_decide

theorem directions : DirectionCheck 61 lineAt :=
  OpenMathConstructionBoolean.directions_sound 61 lineAt directions_bool

theorem simple : SimpleCheck 61 lo hi 29 lineAt :=
  OpenMathConstructionPareto61Fast.intSimple_transfer
    (OpenMathIntegerBoxes.simple_sound OpenMathConstructionPareto61Fast.gridDen
      (by norm_num [OpenMathConstructionPareto61Fast.gridDen]) 61
      OpenMathConstructionPareto61Fast.loInt OpenMathConstructionPareto61Fast.hiInt 29
      OpenMathConstructionPareto61Fast.intLineAt OpenMathConstructionPareto61Fast.int_simple_bool)
#print axioms simple
end Kobon.OpenMathConstructionPareto61
