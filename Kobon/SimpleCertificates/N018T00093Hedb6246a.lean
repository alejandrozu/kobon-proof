import Kobon.Simple
import Kobon.Certificates.N018T00093Hedb6246a

namespace Kobon.Certificates.N018T00093Hedb6246a
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem no_concurrent : NoConcurrent 18 (linesAt lines) := by native_decide

theorem simple_lower_bound : SimpleLowerBound 18 93 :=
  validate_simple_sound lines triangles 93 checked no_concurrent

#print axioms simple_lower_bound
end Kobon.Certificates.N018T00093Hedb6246a
