import Kobon.BBLSeed49Data
import Kobon.OpenMathConstructionBoolean

namespace Kobon.BBLSeed49
open Parametric
set_option maxRecDepth 4096
set_option maxHeartbeats 0
set_option trace.profiler true

theorem directions_bool :
    OpenMathConstructionBoolean.directionsBool 49 lineAt = true := by native_decide

theorem directions_probe : DirectionCheck 49 lineAt :=
  OpenMathConstructionBoolean.directions_sound 49 lineAt directions_bool
#print axioms directions_probe

theorem simple_bool :
    OpenMathConstructionBoolean.simpleBool 49 lo hi 23 lineAt = true := by native_decide

theorem simple_probe : SimpleCheck 49 lo hi 23 lineAt :=
  OpenMathConstructionBoolean.simple_sound 49 lo hi 23 lineAt simple_bool
#print axioms simple_probe

theorem triangles_ten_probe :
    OpenMathConstructionBoolean.trianglesBool 49 lo hi lineAt (triangles.take 10) = true := by
  native_decide
#print axioms triangles_ten_probe

end Kobon.BBLSeed49
