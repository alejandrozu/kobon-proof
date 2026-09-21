import Kobon.Simple
import Kobon.Certificates.N044T00608Hb5277675

namespace Kobon.Certificates.N044T00608Hb5277675
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem no_concurrent : NoConcurrent 44 (linesAt lines) := by native_decide

theorem simple_lower_bound : SimpleLowerBound 44 608 :=
  validate_simple_sound lines triangles 608 checked no_concurrent

#print axioms simple_lower_bound
end Kobon.Certificates.N044T00608Hb5277675
