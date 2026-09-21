import Kobon.Simple
import Kobon.Certificates.N007T00010H4b5bb6e9

namespace Kobon.Certificates.N007T00010H4b5bb6e9
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem no_concurrent : NoConcurrent 7 (linesAt lines) := by native_decide

theorem simple_lower_bound : SimpleLowerBound 7 10 :=
  validate_simple_sound lines triangles 10 checked no_concurrent

#print axioms simple_lower_bound
end Kobon.Certificates.N007T00010H4b5bb6e9
