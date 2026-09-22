import Kobon.Simple
import Kobon.Certificates.N060T01141H9bc5096c

namespace Kobon.Certificates.N060T01141H9bc5096c
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem no_concurrent : NoConcurrent 60 (linesAt lines) := by native_decide

theorem simple_lower_bound : SimpleLowerBound 60 1141 :=
  validate_simple_sound lines triangles 1141 checked no_concurrent

#print axioms simple_lower_bound
end Kobon.Certificates.N060T01141H9bc5096c
