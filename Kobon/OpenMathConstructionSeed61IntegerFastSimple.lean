import Kobon.OpenMathConstructionSeed61IntegerFastRaw
namespace Kobon.OpenMathConstructionSeed61Fast
open OpenMathIntegerBoxes
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false
#eval IO.FS.writeFile "work/openmath-2026-10-05/61-integer-fast-simple-start.txt" "PASS"
theorem int_simple_bool : simpleBool 61 loInt hiInt 29 intLineAt=true := by native_decide
#eval IO.FS.writeFile "work/openmath-2026-10-05/61-integer-fast-simple-pass.txt" "PASS"
#print axioms int_simple_bool
end Kobon.OpenMathConstructionSeed61Fast
