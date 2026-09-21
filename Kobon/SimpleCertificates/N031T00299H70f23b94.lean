import Kobon.Simple
import Kobon.Certificates.N031T00299H70f23b94

namespace Kobon.Certificates.N031T00299H70f23b94
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem no_concurrent : NoConcurrent 31 (linesAt lines) := by native_decide

theorem simple_lower_bound : SimpleLowerBound 31 299 :=
  validate_simple_sound lines triangles 299 checked no_concurrent

#print axioms simple_lower_bound
end Kobon.Certificates.N031T00299H70f23b94
