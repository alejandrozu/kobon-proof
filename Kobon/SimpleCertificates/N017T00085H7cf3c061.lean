import Kobon.Simple
import Kobon.Certificates.N017T00085H7cf3c061

namespace Kobon.Certificates.N017T00085H7cf3c061
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem no_concurrent : NoConcurrent 17 (linesAt lines) := by native_decide

theorem simple_lower_bound : SimpleLowerBound 17 85 :=
  validate_simple_sound lines triangles 85 checked no_concurrent

#print axioms simple_lower_bound
end Kobon.Certificates.N017T00085H7cf3c061
