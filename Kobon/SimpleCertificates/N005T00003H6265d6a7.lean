import Kobon.Simple
import Kobon.Certificates.N005T00003H6265d6a7

namespace Kobon.Certificates.N005T00003H6265d6a7
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem no_concurrent : NoConcurrent 5 (linesAt lines) := by native_decide

theorem simple_lower_bound : SimpleLowerBound 5 3 :=
  validate_simple_sound lines triangles 3 checked no_concurrent

#print axioms simple_lower_bound
end Kobon.Certificates.N005T00003H6265d6a7
