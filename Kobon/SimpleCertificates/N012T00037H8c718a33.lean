import Kobon.Simple
import Kobon.Certificates.N012T00037H8c718a33

namespace Kobon.Certificates.N012T00037H8c718a33
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem no_concurrent : NoConcurrent 12 (linesAt lines) := by native_decide

theorem simple_lower_bound : SimpleLowerBound 12 37 :=
  validate_simple_sound lines triangles 37 checked no_concurrent

#print axioms simple_lower_bound
end Kobon.Certificates.N012T00037H8c718a33
