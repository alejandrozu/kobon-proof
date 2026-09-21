import Kobon.Geometry

namespace Kobon.Certificates.N005T00003H6265d6a7

set_option maxRecDepth 100000
set_option maxHeartbeats 0

def lines : Array (Line ℤ) := #[
  ⟨0,1,0⟩,
  ⟨1,-1,-1⟩,
  ⟨2,-1,-4⟩,
  ⟨3,-1,-9⟩,
  ⟨4,-1,-16⟩
]

def triangles : List Triple := [
  ⟨0,1,2⟩,
  ⟨1,2,3⟩,
  ⟨2,3,4⟩
]

theorem checked : validate lines triangles 3 = true := by native_decide

theorem lower_bound : LowerBound 5 3 :=
  validate_sound lines triangles 3 checked

#print axioms checked
#print axioms lower_bound

end Kobon.Certificates.N005T00003H6265d6a7
