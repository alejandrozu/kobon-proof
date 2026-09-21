import Kobon.Simple
import Kobon.Certificates.N030T00275Hdcfe649a

namespace Kobon.Certificates.N030T00275Hdcfe649a
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem no_concurrent : NoConcurrent 30 (linesAt lines) := by native_decide

theorem simple_lower_bound : SimpleLowerBound 30 275 :=
  validate_simple_sound lines triangles 275 checked no_concurrent

#print axioms simple_lower_bound
end Kobon.Certificates.N030T00275Hdcfe649a
