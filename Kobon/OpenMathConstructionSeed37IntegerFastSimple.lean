import Kobon.OpenMathConstructionSeed37IntegerFastRaw
namespace Kobon.OpenMathConstructionSeed37Fast
open OpenMathIntegerBoxes
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false
theorem int_simple_bool : simpleBool 37 loInt hiInt 17 intLineAt=true := by native_decide
#print axioms int_simple_bool
end Kobon.OpenMathConstructionSeed37Fast
