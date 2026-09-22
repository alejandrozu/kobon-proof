import Kobon.Simple
import Kobon.Certificates.N036T00402Hce43a107

namespace Kobon.Certificates.N036T00402Hce43a107
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem no_concurrent : NoConcurrent 36 (linesAt lines) := by native_decide

theorem simple_lower_bound : SimpleLowerBound 36 402 :=
  validate_simple_sound lines triangles 402 checked no_concurrent

#print axioms simple_lower_bound
end Kobon.Certificates.N036T00402Hce43a107
