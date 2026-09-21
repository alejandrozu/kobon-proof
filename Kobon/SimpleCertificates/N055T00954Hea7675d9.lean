import Kobon.Simple
import Kobon.Certificates.N055T00954Hea7675d9

namespace Kobon.Certificates.N055T00954Hea7675d9
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem no_concurrent : NoConcurrent 55 (linesAt lines) := by native_decide

theorem simple_lower_bound : SimpleLowerBound 55 954 :=
  validate_simple_sound lines triangles 954 checked no_concurrent

#print axioms simple_lower_bound
end Kobon.Certificates.N055T00954Hea7675d9
