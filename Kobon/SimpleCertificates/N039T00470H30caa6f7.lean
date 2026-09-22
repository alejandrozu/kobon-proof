import Kobon.Simple
import Kobon.Certificates.N039T00470H30caa6f7

namespace Kobon.Certificates.N039T00470H30caa6f7
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem no_concurrent : NoConcurrent 39 (linesAt lines) := by native_decide

theorem simple_lower_bound : SimpleLowerBound 39 470 :=
  validate_simple_sound lines triangles 470 checked no_concurrent

#print axioms simple_lower_bound
end Kobon.Certificates.N039T00470H30caa6f7
