import Kobon.Simple
import Kobon.Certificates.N026T00203He61b423c

namespace Kobon.Certificates.N026T00203He61b423c
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem no_concurrent : NoConcurrent 26 (linesAt lines) := by native_decide

theorem simple_lower_bound : SimpleLowerBound 26 203 :=
  validate_simple_sound lines triangles 203 checked no_concurrent

#print axioms simple_lower_bound
end Kobon.Certificates.N026T00203He61b423c
