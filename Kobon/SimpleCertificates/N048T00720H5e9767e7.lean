import Kobon.Simple
import Kobon.Certificates.N048T00720H5e9767e7

namespace Kobon.Certificates.N048T00720H5e9767e7
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem no_concurrent : NoConcurrent 48 (linesAt lines) := by native_decide

theorem simple_lower_bound : SimpleLowerBound 48 720 :=
  validate_simple_sound lines triangles 720 checked no_concurrent

#print axioms simple_lower_bound
end Kobon.Certificates.N048T00720H5e9767e7
