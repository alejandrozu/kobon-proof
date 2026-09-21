import Kobon.Simple
import Kobon.Certificates.N038T00449H46ad5a32

namespace Kobon.Certificates.N038T00449H46ad5a32
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem no_concurrent : NoConcurrent 38 (linesAt lines) := by native_decide

theorem simple_lower_bound : SimpleLowerBound 38 449 :=
  validate_simple_sound lines triangles 449 checked no_concurrent

#print axioms simple_lower_bound
end Kobon.Certificates.N038T00449H46ad5a32
