import Kobon.Simple
import Kobon.Certificates.N066T01397H327ecbb9

namespace Kobon.Certificates.N066T01397H327ecbb9
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem no_concurrent : NoConcurrent 66 (linesAt lines) := by native_decide

theorem simple_lower_bound : SimpleLowerBound 66 1397 :=
  validate_simple_sound lines triangles 1397 checked no_concurrent

#print axioms simple_lower_bound
end Kobon.Certificates.N066T01397H327ecbb9
