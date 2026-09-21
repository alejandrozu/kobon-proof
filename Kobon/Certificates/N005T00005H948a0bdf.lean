import Kobon.Geometry

namespace Kobon.Certificates.N005T00005H948a0bdf

set_option maxRecDepth 100000
set_option maxHeartbeats 0

def lines : Array (Line ℤ) := #[
  ⟨1,2,13⟩,
  ⟨3,2,-55⟩,
  ⟨20324498,2,5543⟩,
  ⟨3,-2,-55⟩,
  ⟨1,-2,13⟩
]

def triangles : List Triple := [
  ⟨0,1,3⟩,
  ⟨0,2,3⟩,
  ⟨0,2,4⟩,
  ⟨1,2,4⟩,
  ⟨1,3,4⟩
]

theorem checked : validate lines triangles 5 = true := by native_decide

theorem lower_bound : LowerBound 5 5 :=
  validate_sound lines triangles 5 checked

#print axioms checked
#print axioms lower_bound

end Kobon.Certificates.N005T00005H948a0bdf
