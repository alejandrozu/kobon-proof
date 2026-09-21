import Kobon.Simple
import Kobon.Certificates.N025T00191Hb568bffb

namespace Kobon.Certificates.N025T00191Hb568bffb
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem no_concurrent : NoConcurrent 25 (linesAt lines) := by native_decide

theorem simple_lower_bound : SimpleLowerBound 25 191 :=
  validate_simple_sound lines triangles 191 checked no_concurrent

#print axioms simple_lower_bound
end Kobon.Certificates.N025T00191Hb568bffb
