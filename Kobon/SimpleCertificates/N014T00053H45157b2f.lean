import Kobon.Simple
import Kobon.Certificates.N014T00053H45157b2f

namespace Kobon.Certificates.N014T00053H45157b2f
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem no_concurrent : NoConcurrent 14 (linesAt lines) := by native_decide

theorem simple_lower_bound : SimpleLowerBound 14 53 :=
  validate_simple_sound lines triangles 53 checked no_concurrent

#print axioms simple_lower_bound
end Kobon.Certificates.N014T00053H45157b2f
