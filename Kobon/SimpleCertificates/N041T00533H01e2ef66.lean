import Kobon.Simple
import Kobon.Certificates.N041T00533H01e2ef66

namespace Kobon.Certificates.N041T00533H01e2ef66
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem no_concurrent : NoConcurrent 41 (linesAt lines) := by native_decide

theorem simple_lower_bound : SimpleLowerBound 41 533 :=
  validate_simple_sound lines triangles 533 checked no_concurrent

#print axioms simple_lower_bound
end Kobon.Certificates.N041T00533H01e2ef66
