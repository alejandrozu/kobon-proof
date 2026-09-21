import Kobon.Simple
import Kobon.Certificates.N051T00816H6fa6b7d9

namespace Kobon.Certificates.N051T00816H6fa6b7d9
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem no_concurrent : NoConcurrent 51 (linesAt lines) := by native_decide

theorem simple_lower_bound : SimpleLowerBound 51 816 :=
  validate_simple_sound lines triangles 816 checked no_concurrent

#print axioms simple_lower_bound
end Kobon.Certificates.N051T00816H6fa6b7d9
