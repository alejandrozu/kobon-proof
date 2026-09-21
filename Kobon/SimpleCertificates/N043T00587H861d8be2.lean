import Kobon.Simple
import Kobon.Certificates.N043T00587H861d8be2

namespace Kobon.Certificates.N043T00587H861d8be2
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem no_concurrent : NoConcurrent 43 (linesAt lines) := by native_decide

theorem simple_lower_bound : SimpleLowerBound 43 587 :=
  validate_simple_sound lines triangles 587 checked no_concurrent

#print axioms simple_lower_bound
end Kobon.Certificates.N043T00587H861d8be2
