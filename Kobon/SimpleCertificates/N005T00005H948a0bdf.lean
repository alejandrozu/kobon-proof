import Kobon.Simple
import Kobon.Certificates.N005T00005H948a0bdf

namespace Kobon.Certificates.N005T00005H948a0bdf
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem no_concurrent : NoConcurrent 5 (linesAt lines) := by native_decide

theorem simple_lower_bound : SimpleLowerBound 5 5 :=
  validate_simple_sound lines triangles 5 checked no_concurrent

#print axioms simple_lower_bound
end Kobon.Certificates.N005T00005H948a0bdf
