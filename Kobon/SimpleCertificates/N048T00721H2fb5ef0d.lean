import Kobon.Simple
import Kobon.Certificates.N048T00721H2fb5ef0d

namespace Kobon.Certificates.N048T00721H2fb5ef0d
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem no_concurrent : NoConcurrent 48 (linesAt lines) := by native_decide

theorem simple_lower_bound : SimpleLowerBound 48 721 :=
  validate_simple_sound lines triangles 721 checked no_concurrent

#print axioms simple_lower_bound
end Kobon.Certificates.N048T00721H2fb5ef0d
