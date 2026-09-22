import Kobon.Simple
import Kobon.Certificates.N053T00885H6bc5b14d

namespace Kobon.Certificates.N053T00885H6bc5b14d
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem no_concurrent : NoConcurrent 53 (linesAt lines) := by native_decide

theorem simple_lower_bound : SimpleLowerBound 53 885 :=
  validate_simple_sound lines triangles 885 checked no_concurrent

#print axioms simple_lower_bound
end Kobon.Certificates.N053T00885H6bc5b14d
