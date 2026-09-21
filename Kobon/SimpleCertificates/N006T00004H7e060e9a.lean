import Kobon.Simple
import Kobon.Certificates.N006T00004H7e060e9a

namespace Kobon.Certificates.N006T00004H7e060e9a
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem no_concurrent : NoConcurrent 6 (linesAt lines) := by native_decide

theorem simple_lower_bound : SimpleLowerBound 6 4 :=
  validate_simple_sound lines triangles 4 checked no_concurrent

#print axioms simple_lower_bound
end Kobon.Certificates.N006T00004H7e060e9a
