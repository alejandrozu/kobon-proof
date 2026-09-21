import Kobon.Simple
import Kobon.Certificates.N013T00047Hddec1f78

namespace Kobon.Certificates.N013T00047Hddec1f78
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem no_concurrent : NoConcurrent 13 (linesAt lines) := by native_decide

theorem simple_lower_bound : SimpleLowerBound 13 47 :=
  validate_simple_sound lines triangles 47 checked no_concurrent

#print axioms simple_lower_bound
end Kobon.Certificates.N013T00047Hddec1f78
