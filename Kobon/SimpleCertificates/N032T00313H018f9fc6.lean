import Kobon.Simple
import Kobon.Certificates.N032T00313H018f9fc6

namespace Kobon.Certificates.N032T00313H018f9fc6
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem no_concurrent : NoConcurrent 32 (linesAt lines) := by native_decide

theorem simple_lower_bound : SimpleLowerBound 32 313 :=
  validate_simple_sound lines triangles 313 checked no_concurrent

#print axioms simple_lower_bound
end Kobon.Certificates.N032T00313H018f9fc6
