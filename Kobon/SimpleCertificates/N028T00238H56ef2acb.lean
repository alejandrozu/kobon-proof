import Kobon.Simple
import Kobon.Certificates.N028T00238H56ef2acb

namespace Kobon.Certificates.N028T00238H56ef2acb
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem no_concurrent : NoConcurrent 28 (linesAt lines) := by native_decide

theorem simple_lower_bound : SimpleLowerBound 28 238 :=
  validate_simple_sound lines triangles 238 checked no_concurrent

#print axioms simple_lower_bound
end Kobon.Certificates.N028T00238H56ef2acb
