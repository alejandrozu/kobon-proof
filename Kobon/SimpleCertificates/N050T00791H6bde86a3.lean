import Kobon.Simple
import Kobon.Certificates.N050T00791H6bde86a3

namespace Kobon.Certificates.N050T00791H6bde86a3
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem no_concurrent : NoConcurrent 50 (linesAt lines) := by native_decide

theorem simple_lower_bound : SimpleLowerBound 50 791 :=
  validate_simple_sound lines triangles 791 checked no_concurrent

#print axioms simple_lower_bound
end Kobon.Certificates.N050T00791H6bde86a3
