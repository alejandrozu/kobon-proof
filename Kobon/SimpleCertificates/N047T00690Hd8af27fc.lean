import Kobon.Simple
import Kobon.Certificates.N047T00690Hd8af27fc

namespace Kobon.Certificates.N047T00690Hd8af27fc
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem no_concurrent : NoConcurrent 47 (linesAt lines) := by native_decide

theorem simple_lower_bound : SimpleLowerBound 47 690 :=
  validate_simple_sound lines triangles 690 checked no_concurrent

#print axioms simple_lower_bound
end Kobon.Certificates.N047T00690Hd8af27fc
