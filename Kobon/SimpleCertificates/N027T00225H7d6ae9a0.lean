import Kobon.Simple
import Kobon.Certificates.N027T00225H7d6ae9a0

namespace Kobon.Certificates.N027T00225H7d6ae9a0
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem no_concurrent : NoConcurrent 27 (linesAt lines) := by native_decide

theorem simple_lower_bound : SimpleLowerBound 27 225 :=
  validate_simple_sound lines triangles 225 checked no_concurrent

#print axioms simple_lower_bound
end Kobon.Certificates.N027T00225H7d6ae9a0
