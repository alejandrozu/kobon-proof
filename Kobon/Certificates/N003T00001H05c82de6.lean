import Kobon.Geometry

namespace Kobon.Certificates.N003T00001H05c82de6

set_option maxRecDepth 100000
set_option maxHeartbeats 0

def lines : Array (Line ℤ) := #[
  ⟨24999999999999997,43301270189221935,50000000000000000⟩,
  ⟨50000000000000000000000000000000,3061616997868383,-50000000000000000000000000000000⟩,
  ⟨24999999999999997,-43301270189221935,50000000000000000⟩
]

def triangles : List Triple := [
  ⟨0,1,2⟩
]

theorem checked : validate lines triangles 1 = true := by native_decide

theorem lower_bound : LowerBound 3 1 :=
  validate_sound lines triangles 1 checked

#print axioms checked
#print axioms lower_bound

end Kobon.Certificates.N003T00001H05c82de6
