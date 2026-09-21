import Kobon.Simple
import Kobon.Certificates.N007T00011He6b9a626

namespace Kobon.Certificates.N007T00011He6b9a626
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem no_concurrent : NoConcurrent 7 (linesAt lines) := by native_decide

theorem simple_lower_bound : SimpleLowerBound 7 11 :=
  validate_simple_sound lines triangles 11 checked no_concurrent

#print axioms simple_lower_bound
end Kobon.Certificates.N007T00011He6b9a626
