import Kobon.Simple
import Kobon.Certificates.N015T00065H4d3bf3b4

namespace Kobon.Certificates.N015T00065H4d3bf3b4
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem no_concurrent : NoConcurrent 15 (linesAt lines) := by native_decide

theorem simple_lower_bound : SimpleLowerBound 15 65 :=
  validate_simple_sound lines triangles 65 checked no_concurrent

#print axioms simple_lower_bound
end Kobon.Certificates.N015T00065H4d3bf3b4
