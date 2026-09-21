import Kobon.Simple
import Kobon.Certificates.N019T00107H5d2a7588

namespace Kobon.Certificates.N019T00107H5d2a7588
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem no_concurrent : NoConcurrent 19 (linesAt lines) := by native_decide

theorem simple_lower_bound : SimpleLowerBound 19 107 :=
  validate_simple_sound lines triangles 107 checked no_concurrent

#print axioms simple_lower_bound
end Kobon.Certificates.N019T00107H5d2a7588
