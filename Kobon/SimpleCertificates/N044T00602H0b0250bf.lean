import Kobon.Simple
import Kobon.Certificates.N044T00602H0b0250bf

namespace Kobon.Certificates.N044T00602H0b0250bf
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem no_concurrent : NoConcurrent 44 (linesAt lines) := by native_decide

theorem simple_lower_bound : SimpleLowerBound 44 602 :=
  validate_simple_sound lines triangles 602 checked no_concurrent

#print axioms simple_lower_bound
end Kobon.Certificates.N044T00602H0b0250bf
