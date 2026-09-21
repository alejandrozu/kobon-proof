import Kobon.Simple
import Kobon.Certificates.N006T00007H6ea9ebaa

namespace Kobon.Certificates.N006T00007H6ea9ebaa
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem no_concurrent : NoConcurrent 6 (linesAt lines) := by native_decide

theorem simple_lower_bound : SimpleLowerBound 6 7 :=
  validate_simple_sound lines triangles 7 checked no_concurrent

#print axioms simple_lower_bound
end Kobon.Certificates.N006T00007H6ea9ebaa
