import Kobon.Geometry

namespace Kobon.Certificates.N006T00004H7e060e9a

set_option maxRecDepth 100000
set_option maxHeartbeats 0

def lines : Array (Line ℤ) := #[
  ⟨0,1,0⟩,
  ⟨1,-1,-1⟩,
  ⟨2,-1,-4⟩,
  ⟨3,-1,-9⟩,
  ⟨4,-1,-16⟩,
  ⟨1,-2,-200⟩
]

def triangles : List Triple := [
  ⟨0,1,2⟩,
  ⟨0,4,5⟩,
  ⟨1,2,3⟩,
  ⟨2,3,4⟩
]

theorem checked : validate lines triangles 4 = true := by native_decide

theorem lower_bound : LowerBound 6 4 :=
  validate_sound lines triangles 4 checked

#print axioms checked
#print axioms lower_bound

end Kobon.Certificates.N006T00004H7e060e9a
