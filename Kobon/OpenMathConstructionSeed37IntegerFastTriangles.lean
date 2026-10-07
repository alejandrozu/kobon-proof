import Kobon.OpenMathConstructionSeed37Data
import Kobon.OpenMathConstructionSeed37IntegerFastRaw
namespace Kobon.OpenMathConstructionSeed37Fast
open OpenMathIntegerBoxes OpenMathConstructionSeed37
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false
theorem int_triangles_bool : trianglesBool 37 loInt hiInt intLineAt triangles=true := by native_decide
#print axioms int_triangles_bool
end Kobon.OpenMathConstructionSeed37Fast
