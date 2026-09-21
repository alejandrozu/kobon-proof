import Kobon.Simple
import Kobon.Certificates.N016T00072H391cf79a

namespace Kobon.Certificates.N016T00072H391cf79a
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem no_concurrent : NoConcurrent 16 (linesAt lines) := by native_decide

theorem simple_lower_bound : SimpleLowerBound 16 72 :=
  validate_simple_sound lines triangles 72 checked no_concurrent

#print axioms simple_lower_bound
end Kobon.Certificates.N016T00072H391cf79a
