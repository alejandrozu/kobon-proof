import Kobon.Simple
import Kobon.Certificates.N053T00884H723d7eff

namespace Kobon.Certificates.N053T00884H723d7eff
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem no_concurrent : NoConcurrent 53 (linesAt lines) := by native_decide

theorem simple_lower_bound : SimpleLowerBound 53 884 :=
  validate_simple_sound lines triangles 884 checked no_concurrent

#print axioms simple_lower_bound
end Kobon.Certificates.N053T00884H723d7eff
