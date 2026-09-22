import Kobon.Simple
import Kobon.Certificates.N051T00818Hc18e1baf

namespace Kobon.Certificates.N051T00818Hc18e1baf
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem no_concurrent : NoConcurrent 51 (linesAt lines) := by native_decide

theorem simple_lower_bound : SimpleLowerBound 51 818 :=
  validate_simple_sound lines triangles 818 checked no_concurrent

#print axioms simple_lower_bound
end Kobon.Certificates.N051T00818Hc18e1baf
