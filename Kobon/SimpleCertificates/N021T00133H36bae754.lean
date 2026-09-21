import Kobon.Simple
import Kobon.Certificates.N021T00133H36bae754

namespace Kobon.Certificates.N021T00133H36bae754
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem no_concurrent : NoConcurrent 21 (linesAt lines) := by native_decide

theorem simple_lower_bound : SimpleLowerBound 21 133 :=
  validate_simple_sound lines triangles 133 checked no_concurrent

#print axioms simple_lower_bound
end Kobon.Certificates.N021T00133H36bae754
