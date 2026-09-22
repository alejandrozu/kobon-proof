import Kobon.Simple
import Kobon.Certificates.N055T00955H202625a3

namespace Kobon.Certificates.N055T00955H202625a3
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem no_concurrent : NoConcurrent 55 (linesAt lines) := by native_decide

theorem simple_lower_bound : SimpleLowerBound 55 955 :=
  validate_simple_sound lines triangles 955 checked no_concurrent

#print axioms simple_lower_bound
end Kobon.Certificates.N055T00955H202625a3
