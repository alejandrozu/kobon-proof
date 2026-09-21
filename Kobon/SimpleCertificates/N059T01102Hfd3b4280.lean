import Kobon.Simple
import Kobon.Certificates.N059T01102Hfd3b4280

namespace Kobon.Certificates.N059T01102Hfd3b4280
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem no_concurrent : NoConcurrent 59 (linesAt lines) := by native_decide

theorem simple_lower_bound : SimpleLowerBound 59 1102 :=
  validate_simple_sound lines triangles 1102 checked no_concurrent

#print axioms simple_lower_bound
end Kobon.Certificates.N059T01102Hfd3b4280
