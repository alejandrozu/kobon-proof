import Kobon.Simple
import Kobon.Certificates.N099T03168Ha0ea3082

namespace Kobon.Certificates.N099T03168Ha0ea3082
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem no_concurrent : NoConcurrent 99 (linesAt lines) := by native_decide

theorem simple_lower_bound : SimpleLowerBound 99 3168 :=
  validate_simple_sound lines triangles 3168 checked no_concurrent

#print axioms simple_lower_bound
end Kobon.Certificates.N099T03168Ha0ea3082
