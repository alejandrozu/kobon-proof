import Kobon.Simple
import Kobon.Certificates.N058T01073Hd988db55

namespace Kobon.Certificates.N058T01073Hd988db55
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem no_concurrent : NoConcurrent 58 (linesAt lines) := by native_decide

theorem simple_lower_bound : SimpleLowerBound 58 1073 :=
  validate_simple_sound lines triangles 1073 checked no_concurrent

#print axioms simple_lower_bound
end Kobon.Certificates.N058T01073Hd988db55
