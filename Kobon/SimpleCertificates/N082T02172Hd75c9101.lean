import Kobon.Simple
import Kobon.Certificates.N082T02172Hd75c9101

namespace Kobon.Certificates.N082T02172Hd75c9101
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem no_concurrent : NoConcurrent 82 (linesAt lines) := by native_decide

theorem simple_lower_bound : SimpleLowerBound 82 2172 :=
  validate_simple_sound lines triangles 2172 checked no_concurrent

#print axioms simple_lower_bound
end Kobon.Certificates.N082T02172Hd75c9101
