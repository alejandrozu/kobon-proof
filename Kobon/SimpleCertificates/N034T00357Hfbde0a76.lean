import Kobon.Simple
import Kobon.Certificates.N034T00357Hfbde0a76

namespace Kobon.Certificates.N034T00357Hfbde0a76
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem no_concurrent : NoConcurrent 34 (linesAt lines) := by native_decide

theorem simple_lower_bound : SimpleLowerBound 34 357 :=
  validate_simple_sound lines triangles 357 checked no_concurrent

#print axioms simple_lower_bound
end Kobon.Certificates.N034T00357Hfbde0a76
