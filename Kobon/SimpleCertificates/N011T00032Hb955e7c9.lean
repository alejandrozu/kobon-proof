import Kobon.Simple
import Kobon.Certificates.N011T00032Hb955e7c9

namespace Kobon.Certificates.N011T00032Hb955e7c9
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem no_concurrent : NoConcurrent 11 (linesAt lines) := by native_decide

theorem simple_lower_bound : SimpleLowerBound 11 32 :=
  validate_simple_sound lines triangles 32 checked no_concurrent

#print axioms simple_lower_bound
end Kobon.Certificates.N011T00032Hb955e7c9
