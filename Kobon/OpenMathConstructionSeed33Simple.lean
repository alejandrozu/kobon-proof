import Kobon.OpenMathConstructionSeed33Data
import Kobon.OpenMathConstructionBooleanMemo
namespace Kobon.OpenMathConstructionSeed33
open Parametric
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option trace.profiler true
set_option Elab.async false

 theorem directions_bool : OpenMathConstructionBoolean.directionsBool 33 lineAt=true := by
   native_decide

 theorem directions : DirectionCheck 33 lineAt :=
   OpenMathConstructionBoolean.directions_sound 33 lineAt directions_bool

#print axioms directions
#eval do
  IO.println "33 directions complete; starting Boolean simplicity"
  (← IO.getStdout).flush

 theorem simple_bool : OpenMathConstructionBooleanMemo.simpleBool 33 lo hi 15 lineAt=true := by
   native_decide

 theorem simple : SimpleCheck 33 lo hi 15 lineAt :=
   OpenMathConstructionBooleanMemo.simple_sound 33 lo hi 15 lineAt simple_bool

#print axioms simple
end Kobon.OpenMathConstructionSeed33