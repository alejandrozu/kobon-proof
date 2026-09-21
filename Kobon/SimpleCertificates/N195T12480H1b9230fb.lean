import Kobon.Simple
import Kobon.Certificates.N195T12480H1b9230fb

namespace Kobon.Certificates.N195T12480H1b9230fb
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem no_concurrent : NoConcurrent 195 (linesAt lines) := by native_decide

theorem simple_lower_bound : SimpleLowerBound 195 12480 :=
  validate_simple_sound lines triangles 12480 checked no_concurrent

#print axioms simple_lower_bound
end Kobon.Certificates.N195T12480H1b9230fb
