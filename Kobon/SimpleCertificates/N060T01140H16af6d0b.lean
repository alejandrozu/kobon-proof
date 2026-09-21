import Kobon.Simple
import Kobon.Certificates.N060T01140H16af6d0b

namespace Kobon.Certificates.N060T01140H16af6d0b
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem no_concurrent : NoConcurrent 60 (linesAt lines) := by native_decide

theorem simple_lower_bound : SimpleLowerBound 60 1140 :=
  validate_simple_sound lines triangles 1140 checked no_concurrent

#print axioms simple_lower_bound
end Kobon.Certificates.N060T01140H16af6d0b
