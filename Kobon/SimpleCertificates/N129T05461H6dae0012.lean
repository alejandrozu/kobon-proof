import Kobon.Simple
import Kobon.Certificates.N129T05461H6dae0012

namespace Kobon.Certificates.N129T05461H6dae0012
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem no_concurrent : NoConcurrent 129 (linesAt lines) := by native_decide

theorem simple_lower_bound : SimpleLowerBound 129 5461 :=
  validate_simple_sound lines triangles 5461 checked no_concurrent

#print axioms simple_lower_bound
end Kobon.Certificates.N129T05461H6dae0012
