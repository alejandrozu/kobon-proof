import Kobon.Simple
import Kobon.Certificates.N161T08532H230691d5

namespace Kobon.Certificates.N161T08532H230691d5
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem no_concurrent : NoConcurrent 161 (linesAt lines) := by native_decide

theorem simple_lower_bound : SimpleLowerBound 161 8532 :=
  validate_simple_sound lines triangles 8532 checked no_concurrent

#print axioms simple_lower_bound
end Kobon.Certificates.N161T08532H230691d5
