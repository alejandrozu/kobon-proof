import Kobon.Simple
import Kobon.Certificates.N008T00014H2a63f4d9

namespace Kobon.Certificates.N008T00014H2a63f4d9
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem no_concurrent : NoConcurrent 8 (linesAt lines) := by native_decide

theorem simple_lower_bound : SimpleLowerBound 8 14 :=
  validate_simple_sound lines triangles 14 checked no_concurrent

#print axioms simple_lower_bound
end Kobon.Certificates.N008T00014H2a63f4d9
