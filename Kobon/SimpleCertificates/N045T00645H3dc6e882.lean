import Kobon.Simple
import Kobon.Certificates.N045T00645H3dc6e882

namespace Kobon.Certificates.N045T00645H3dc6e882
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem no_concurrent : NoConcurrent 45 (linesAt lines) := by native_decide

theorem simple_lower_bound : SimpleLowerBound 45 645 :=
  validate_simple_sound lines triangles 645 checked no_concurrent

#print axioms simple_lower_bound
end Kobon.Certificates.N045T00645H3dc6e882
