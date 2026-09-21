import Kobon.Simple
import Kobon.Certificates.N003T00001H05c82de6

namespace Kobon.Certificates.N003T00001H05c82de6
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem no_concurrent : NoConcurrent 3 (linesAt lines) := by native_decide

theorem simple_lower_bound : SimpleLowerBound 3 1 :=
  validate_simple_sound lines triangles 1 checked no_concurrent

#print axioms simple_lower_bound
end Kobon.Certificates.N003T00001H05c82de6
