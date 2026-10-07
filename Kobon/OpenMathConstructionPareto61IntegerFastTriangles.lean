import Kobon.OpenMathConstructionPareto61Data
import Kobon.OpenMathConstructionPareto61IntegerFastRaw
namespace Kobon.OpenMathConstructionPareto61Fast
open OpenMathIntegerBoxes OpenMathConstructionPareto61
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false
theorem int_triangles_bool : trianglesBool 61 loInt hiInt intLineAt triangles=true := by native_decide
#print axioms int_triangles_bool
end Kobon.OpenMathConstructionPareto61Fast
