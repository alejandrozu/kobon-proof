import Kobon.Geometry

namespace Kobon.Certificates.N005T00005Hdd0748b7

set_option maxRecDepth 100000
set_option maxHeartbeats 0

def lines : Array (Line ℤ) := #[
  ⟨0,1,0⟩,
  ⟨1,-1,-1⟩,
  ⟨2,-1,-4⟩,
  ⟨3,-1,-9⟩,
  ⟨7,-6,-15⟩
]

def triangles : List Triple := [
  ⟨0,1,2⟩,
  ⟨0,2,4⟩,
  ⟨0,3,4⟩,
  ⟨1,2,3⟩,
  ⟨1,3,4⟩
]

theorem checked : validate lines triangles 5 = true := by native_decide

theorem lower_bound : LowerBound 5 5 :=
  validate_sound lines triangles 5 checked

#print axioms checked
#print axioms lower_bound

end Kobon.Certificates.N005T00005Hdd0748b7
