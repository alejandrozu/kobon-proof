import Kobon.Simple
import Kobon.Certificates.N033T00341H95f3b770

namespace Kobon.Certificates.N033T00341H95f3b770
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem no_concurrent : NoConcurrent 33 (linesAt lines) := by native_decide

theorem simple_lower_bound : SimpleLowerBound 33 341 :=
  validate_simple_sound lines triangles 341 checked no_concurrent

#print axioms simple_lower_bound
end Kobon.Certificates.N033T00341H95f3b770
