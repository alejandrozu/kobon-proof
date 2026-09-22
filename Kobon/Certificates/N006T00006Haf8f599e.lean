import Kobon.Geometry

namespace Kobon.Certificates.N006T00006Haf8f599e

set_option maxRecDepth 100000
set_option maxHeartbeats 0

def lines : Array (Line ℤ) := #[
  ⟨1,0,0⟩,
  ⟨0,1,0⟩,
  ⟨1,1,3⟩,
  ⟨1,-1,0⟩,
  ⟨2,1,3⟩,
  ⟨1,2,3⟩
]

def triangles : List Triple := [
  ⟨0,3,5⟩,
  ⟨0,4,5⟩,
  ⟨1,3,4⟩,
  ⟨1,4,5⟩,
  ⟨2,3,4⟩,
  ⟨2,3,5⟩
]

theorem checked : validate lines triangles 6 = true := by native_decide

theorem lower_bound : LowerBound 6 6 :=
  validate_sound lines triangles 6 checked

#print axioms checked
#print axioms lower_bound

end Kobon.Certificates.N006T00006Haf8f599e
