import Kobon.Simple
import Kobon.Certificates.N042T00552H7b29a6bd

namespace Kobon.Certificates.N042T00552H7b29a6bd
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem no_concurrent : NoConcurrent 42 (linesAt lines) := by native_decide

theorem simple_lower_bound : SimpleLowerBound 42 552 :=
  validate_simple_sound lines triangles 552 checked no_concurrent

#print axioms simple_lower_bound
end Kobon.Certificates.N042T00552H7b29a6bd
