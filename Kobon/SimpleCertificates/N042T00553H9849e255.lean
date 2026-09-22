import Kobon.Simple
import Kobon.Certificates.N042T00553H9849e255

namespace Kobon.Certificates.N042T00553H9849e255
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem no_concurrent : NoConcurrent 42 (linesAt lines) := by native_decide

theorem simple_lower_bound : SimpleLowerBound 42 553 :=
  validate_simple_sound lines triangles 553 checked no_concurrent

#print axioms simple_lower_bound
end Kobon.Certificates.N042T00553H9849e255
