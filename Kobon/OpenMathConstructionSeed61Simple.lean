import Kobon.OpenMathConstructionSeed61IntegerFastData
import Kobon.OpenMathConstructionSeed61IntegerFastSimple
namespace Kobon.OpenMathConstructionSeed61
open Parametric HybridBoundary
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

theorem directions_bool : OpenMathConstructionBoolean.directionsBool 61 lineAt=true := by native_decide

theorem directions : DirectionCheck 61 lineAt :=
  OpenMathConstructionBoolean.directions_sound 61 lineAt directions_bool

theorem simple : SimpleCheck 61 lo hi 29 lineAt :=
  OpenMathConstructionSeed61Fast.intSimple_transfer
    (OpenMathIntegerBoxes.simple_sound OpenMathConstructionSeed61Fast.gridDen
      (by norm_num [OpenMathConstructionSeed61Fast.gridDen]) 61
      OpenMathConstructionSeed61Fast.loInt OpenMathConstructionSeed61Fast.hiInt 29
      OpenMathConstructionSeed61Fast.intLineAt OpenMathConstructionSeed61Fast.int_simple_bool)
#print axioms simple
end Kobon.OpenMathConstructionSeed61
