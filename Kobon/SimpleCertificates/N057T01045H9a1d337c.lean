import Kobon.Simple
import Kobon.Certificates.N057T01045H9a1d337c

namespace Kobon.Certificates.N057T01045H9a1d337c
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem no_concurrent : NoConcurrent 57 (linesAt lines) := by native_decide

theorem simple_lower_bound : SimpleLowerBound 57 1045 :=
  validate_simple_sound lines triangles 1045 checked no_concurrent

#print axioms simple_lower_bound
end Kobon.Certificates.N057T01045H9a1d337c
