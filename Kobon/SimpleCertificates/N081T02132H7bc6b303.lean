import Kobon.Simple
import Kobon.Certificates.N081T02132H7bc6b303

namespace Kobon.Certificates.N081T02132H7bc6b303
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem no_concurrent : NoConcurrent 81 (linesAt lines) := by native_decide

theorem simple_lower_bound : SimpleLowerBound 81 2132 :=
  validate_simple_sound lines triangles 2132 checked no_concurrent

#print axioms simple_lower_bound
end Kobon.Certificates.N081T02132H7bc6b303
