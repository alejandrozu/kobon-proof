import Kobon.Simple
import Kobon.Certificates.N004T00002H0e541bd5

namespace Kobon.Certificates.N004T00002H0e541bd5
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem no_concurrent : NoConcurrent 4 (linesAt lines) := by native_decide

theorem simple_lower_bound : SimpleLowerBound 4 2 :=
  validate_simple_sound lines triangles 2 checked no_concurrent

#print axioms simple_lower_bound
end Kobon.Certificates.N004T00002H0e541bd5
