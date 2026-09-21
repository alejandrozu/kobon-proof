import Kobon.Simple
import Kobon.Certificates.N009T00021H6ebbed82

namespace Kobon.Certificates.N009T00021H6ebbed82
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem no_concurrent : NoConcurrent 9 (linesAt lines) := by native_decide

theorem simple_lower_bound : SimpleLowerBound 9 21 :=
  validate_simple_sound lines triangles 21 checked no_concurrent

#print axioms simple_lower_bound
end Kobon.Certificates.N009T00021H6ebbed82
