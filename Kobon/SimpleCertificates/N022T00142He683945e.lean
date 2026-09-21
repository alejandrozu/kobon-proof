import Kobon.Simple
import Kobon.Certificates.N022T00142He683945e

namespace Kobon.Certificates.N022T00142He683945e
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem no_concurrent : NoConcurrent 22 (linesAt lines) := by native_decide

theorem simple_lower_bound : SimpleLowerBound 22 142 :=
  validate_simple_sound lines triangles 142 checked no_concurrent

#print axioms simple_lower_bound
end Kobon.Certificates.N022T00142He683945e
