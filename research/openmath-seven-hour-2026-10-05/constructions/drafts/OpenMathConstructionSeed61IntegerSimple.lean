import Kobon.OpenMathConstructionSeed61IntegerRaw
namespace Kobon.OpenMathConstructionSeed61
open OpenMathIntegerBoxes
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false
set_option trace.profiler false
#eval IO.FS.writeFile "work/openmath-2026-10-05/61-integer-simple-start.txt" "PASS"
theorem int_simple_bool : simpleBool 61 loInt hiInt 29 intLineAt=true := by native_decide
#eval IO.FS.writeFile "work/openmath-2026-10-05/61-integer-simple-pass.txt" "PASS"
#print axioms int_simple_bool
end Kobon.OpenMathConstructionSeed61
