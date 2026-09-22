import Kobon.Simple
import Kobon.Certificates.N065T01365Hb1dcbeb4

namespace Kobon.Certificates.N065T01365Hb1dcbeb4
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem no_concurrent : NoConcurrent 65 (linesAt lines) := by native_decide

theorem simple_lower_bound : SimpleLowerBound 65 1365 :=
  validate_simple_sound lines triangles 1365 checked no_concurrent

#print axioms simple_lower_bound
end Kobon.Certificates.N065T01365Hb1dcbeb4
