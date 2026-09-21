import Kobon.Simple
import Kobon.Certificates.N162T08612H1512e696

namespace Kobon.Certificates.N162T08612H1512e696
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem no_concurrent : NoConcurrent 162 (linesAt lines) := by native_decide

theorem simple_lower_bound : SimpleLowerBound 162 8612 :=
  validate_simple_sound lines triangles 8612 checked no_concurrent

#print axioms simple_lower_bound
end Kobon.Certificates.N162T08612H1512e696
