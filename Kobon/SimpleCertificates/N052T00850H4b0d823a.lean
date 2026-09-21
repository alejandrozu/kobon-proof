import Kobon.Simple
import Kobon.Certificates.N052T00850H4b0d823a

namespace Kobon.Certificates.N052T00850H4b0d823a
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem no_concurrent : NoConcurrent 52 (linesAt lines) := by native_decide

theorem simple_lower_bound : SimpleLowerBound 52 850 :=
  validate_simple_sound lines triangles 850 checked no_concurrent

#print axioms simple_lower_bound
end Kobon.Certificates.N052T00850H4b0d823a
