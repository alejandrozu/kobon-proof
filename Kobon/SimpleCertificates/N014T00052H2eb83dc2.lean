import Kobon.Simple
import Kobon.Certificates.N014T00052H2eb83dc2

namespace Kobon.Certificates.N014T00052H2eb83dc2
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem no_concurrent : NoConcurrent 14 (linesAt lines) := by native_decide

theorem simple_lower_bound : SimpleLowerBound 14 52 :=
  validate_simple_sound lines triangles 52 checked no_concurrent

#print axioms simple_lower_bound
end Kobon.Certificates.N014T00052H2eb83dc2
