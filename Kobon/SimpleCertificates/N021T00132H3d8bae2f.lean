import Kobon.Simple
import Kobon.Certificates.N021T00132H3d8bae2f

namespace Kobon.Certificates.N021T00132H3d8bae2f
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem no_concurrent : NoConcurrent 21 (linesAt lines) := by native_decide

theorem simple_lower_bound : SimpleLowerBound 21 132 :=
  validate_simple_sound lines triangles 132 checked no_concurrent

#print axioms simple_lower_bound
end Kobon.Certificates.N021T00132H3d8bae2f
