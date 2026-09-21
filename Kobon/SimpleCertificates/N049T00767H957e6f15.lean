import Kobon.Simple
import Kobon.Certificates.N049T00767H957e6f15

namespace Kobon.Certificates.N049T00767H957e6f15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem no_concurrent : NoConcurrent 49 (linesAt lines) := by native_decide

theorem simple_lower_bound : SimpleLowerBound 49 767 :=
  validate_simple_sound lines triangles 767 checked no_concurrent

#print axioms simple_lower_bound
end Kobon.Certificates.N049T00767H957e6f15
