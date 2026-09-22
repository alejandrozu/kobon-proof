import Kobon.Simple
import Kobon.Certificates.N130T05525He0559b54

namespace Kobon.Certificates.N130T05525He0559b54
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem no_concurrent : NoConcurrent 130 (linesAt lines) := by native_decide

theorem simple_lower_bound : SimpleLowerBound 130 5525 :=
  validate_simple_sound lines triangles 5525 checked no_concurrent

#print axioms simple_lower_bound
end Kobon.Certificates.N130T05525He0559b54
