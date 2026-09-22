import Kobon.Simple
import Kobon.Certificates.N014T00051Hd67e7a6b

namespace Kobon.Certificates.N014T00051Hd67e7a6b
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem no_concurrent : NoConcurrent 14 (linesAt lines) := by native_decide

theorem simple_lower_bound : SimpleLowerBound 14 51 :=
  validate_simple_sound lines triangles 51 checked no_concurrent

#print axioms simple_lower_bound
end Kobon.Certificates.N014T00051Hd67e7a6b
