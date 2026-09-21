import Kobon.Simple
import Kobon.Certificates.N037T00431H11f0bde7

namespace Kobon.Certificates.N037T00431H11f0bde7
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem no_concurrent : NoConcurrent 37 (linesAt lines) := by native_decide

theorem simple_lower_bound : SimpleLowerBound 37 431 :=
  validate_simple_sound lines triangles 431 checked no_concurrent

#print axioms simple_lower_bound
end Kobon.Certificates.N037T00431H11f0bde7
