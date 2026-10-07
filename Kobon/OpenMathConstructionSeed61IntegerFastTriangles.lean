import Kobon.OpenMathConstructionSeed61Data
import Kobon.OpenMathConstructionSeed61IntegerFastRaw
namespace Kobon.OpenMathConstructionSeed61Fast
open OpenMathIntegerBoxes OpenMathConstructionSeed61
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false
theorem int_triangles_bool : trianglesBool 61 loInt hiInt intLineAt triangles=true := by native_decide
#print axioms int_triangles_bool
end Kobon.OpenMathConstructionSeed61Fast
