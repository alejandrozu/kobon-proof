import Kobon.Simple
import Kobon.Certificates.N039T00468H5c5b0b26

namespace Kobon.Certificates.N039T00468H5c5b0b26
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem no_concurrent : NoConcurrent 39 (linesAt lines) := by native_decide

theorem simple_lower_bound : SimpleLowerBound 39 468 :=
  validate_simple_sound lines triangles 468 checked no_concurrent

#print axioms simple_lower_bound
end Kobon.Certificates.N039T00468H5c5b0b26
