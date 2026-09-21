import Kobon.Simple
import Kobon.Certificates.N040T00494H785374ca

namespace Kobon.Certificates.N040T00494H785374ca
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem no_concurrent : NoConcurrent 40 (linesAt lines) := by native_decide

theorem simple_lower_bound : SimpleLowerBound 40 494 :=
  validate_simple_sound lines triangles 494 checked no_concurrent

#print axioms simple_lower_bound
end Kobon.Certificates.N040T00494H785374ca
