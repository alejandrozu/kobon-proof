import Kobon.Simple
import Kobon.Certificates.N020T00114Hbc312fc8

namespace Kobon.Certificates.N020T00114Hbc312fc8
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem no_concurrent : NoConcurrent 20 (linesAt lines) := by native_decide

theorem simple_lower_bound : SimpleLowerBound 20 114 :=
  validate_simple_sound lines triangles 114 checked no_concurrent

#print axioms simple_lower_bound
end Kobon.Certificates.N020T00114Hbc312fc8
