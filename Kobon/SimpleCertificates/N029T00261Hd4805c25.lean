import Kobon.Simple
import Kobon.Certificates.N029T00261Hd4805c25

namespace Kobon.Certificates.N029T00261Hd4805c25
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem no_concurrent : NoConcurrent 29 (linesAt lines) := by native_decide

theorem simple_lower_bound : SimpleLowerBound 29 261 :=
  validate_simple_sound lines triangles 261 checked no_concurrent

#print axioms simple_lower_bound
end Kobon.Certificates.N029T00261Hd4805c25
