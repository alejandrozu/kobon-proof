import Kobon.Simple
import Kobon.Certificates.N054T00919Ha254c1b4

namespace Kobon.Certificates.N054T00919Ha254c1b4
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem no_concurrent : NoConcurrent 54 (linesAt lines) := by native_decide

theorem simple_lower_bound : SimpleLowerBound 54 919 :=
  validate_simple_sound lines triangles 919 checked no_concurrent

#print axioms simple_lower_bound
end Kobon.Certificates.N054T00919Ha254c1b4
