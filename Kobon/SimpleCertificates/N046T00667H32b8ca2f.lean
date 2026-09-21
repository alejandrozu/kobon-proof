import Kobon.Simple
import Kobon.Certificates.N046T00667H32b8ca2f

namespace Kobon.Certificates.N046T00667H32b8ca2f
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem no_concurrent : NoConcurrent 46 (linesAt lines) := by native_decide

theorem simple_lower_bound : SimpleLowerBound 46 667 :=
  validate_simple_sound lines triangles 667 checked no_concurrent

#print axioms simple_lower_bound
end Kobon.Certificates.N046T00667H32b8ca2f
