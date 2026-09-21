import Kobon.Simple
import Kobon.Certificates.N024T00172He63e906b

namespace Kobon.Certificates.N024T00172He63e906b
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem no_concurrent : NoConcurrent 24 (linesAt lines) := by native_decide

theorem simple_lower_bound : SimpleLowerBound 24 172 :=
  validate_simple_sound lines triangles 172 checked no_concurrent

#print axioms simple_lower_bound
end Kobon.Certificates.N024T00172He63e906b
