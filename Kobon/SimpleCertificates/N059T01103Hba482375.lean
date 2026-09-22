import Kobon.Simple
import Kobon.Certificates.N059T01103Hba482375

namespace Kobon.Certificates.N059T01103Hba482375
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem no_concurrent : NoConcurrent 59 (linesAt lines) := by native_decide

theorem simple_lower_bound : SimpleLowerBound 59 1103 :=
  validate_simple_sound lines triangles 1103 checked no_concurrent

#print axioms simple_lower_bound
end Kobon.Certificates.N059T01103Hba482375
