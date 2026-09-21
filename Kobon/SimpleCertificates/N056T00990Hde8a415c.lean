import Kobon.Simple
import Kobon.Certificates.N056T00990Hde8a415c

namespace Kobon.Certificates.N056T00990Hde8a415c
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem no_concurrent : NoConcurrent 56 (linesAt lines) := by native_decide

theorem simple_lower_bound : SimpleLowerBound 56 990 :=
  validate_simple_sound lines triangles 990 checked no_concurrent

#print axioms simple_lower_bound
end Kobon.Certificates.N056T00990Hde8a415c
