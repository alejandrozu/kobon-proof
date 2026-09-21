import Kobon.Simple
import Kobon.Certificates.N035T00385H9ee99af6

namespace Kobon.Certificates.N035T00385H9ee99af6
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem no_concurrent : NoConcurrent 35 (linesAt lines) := by native_decide

theorem simple_lower_bound : SimpleLowerBound 35 385 :=
  validate_simple_sound lines triangles 385 checked no_concurrent

#print axioms simple_lower_bound
end Kobon.Certificates.N035T00385H9ee99af6
