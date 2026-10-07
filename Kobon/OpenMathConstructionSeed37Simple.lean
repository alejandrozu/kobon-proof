import Kobon.OpenMathConstructionSeed37IntegerFastData
import Kobon.OpenMathConstructionSeed37IntegerFastSimple
namespace Kobon.OpenMathConstructionSeed37
open Parametric HybridBoundary
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

theorem directions_bool : OpenMathConstructionBoolean.directionsBool 37 lineAt=true := by native_decide

theorem directions : DirectionCheck 37 lineAt :=
  OpenMathConstructionBoolean.directions_sound 37 lineAt directions_bool

theorem simple : SimpleCheck 37 lo hi 17 lineAt :=
  OpenMathConstructionSeed37Fast.intSimple_transfer
    (OpenMathIntegerBoxes.simple_sound OpenMathConstructionSeed37Fast.gridDen
      (by norm_num [OpenMathConstructionSeed37Fast.gridDen]) 37
      OpenMathConstructionSeed37Fast.loInt OpenMathConstructionSeed37Fast.hiInt 17
      OpenMathConstructionSeed37Fast.intLineAt OpenMathConstructionSeed37Fast.int_simple_bool)
#print axioms simple
end Kobon.OpenMathConstructionSeed37
