import Kobon.OpenMathConstructionPareto61IntegerFastRaw
namespace Kobon.OpenMathConstructionPareto61Fast
open OpenMathIntegerBoxes
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false
theorem int_simple_bool : simpleBool 61 loInt hiInt 29 intLineAt=true := by native_decide
#print axioms int_simple_bool
end Kobon.OpenMathConstructionPareto61Fast
