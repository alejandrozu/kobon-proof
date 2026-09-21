import Kobon.Simple
import Kobon.Certificates.N023T00161H969ad7d3

namespace Kobon.Certificates.N023T00161H969ad7d3
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem no_concurrent : NoConcurrent 23 (linesAt lines) := by native_decide

theorem simple_lower_bound : SimpleLowerBound 23 161 :=
  validate_simple_sound lines triangles 161 checked no_concurrent

#print axioms simple_lower_bound
end Kobon.Certificates.N023T00161H969ad7d3
