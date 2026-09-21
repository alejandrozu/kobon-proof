import Kobon.Simple
import Kobon.Certificates.N010T00025Hb767c427

namespace Kobon.Certificates.N010T00025Hb767c427
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem no_concurrent : NoConcurrent 10 (linesAt lines) := by native_decide

theorem simple_lower_bound : SimpleLowerBound 10 25 :=
  validate_simple_sound lines triangles 25 checked no_concurrent

#print axioms simple_lower_bound
end Kobon.Certificates.N010T00025Hb767c427
