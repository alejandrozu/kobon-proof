import Kobon.Geometry

namespace Kobon.Certificates.N006T00007H6ea9ebaa

set_option maxRecDepth 100000
set_option maxHeartbeats 0

def lines : Array (Line ℤ) := #[
  ⟨0,1,0⟩,
  ⟨1,-1,-1⟩,
  ⟨2,-1,-4⟩,
  ⟨3,-1,-9⟩,
  ⟨7,-6,-15⟩,
  ⟨28,-19,2⟩
]

def triangles : List Triple := [
  ⟨0,1,2⟩,
  ⟨0,1,5⟩,
  ⟨0,2,4⟩,
  ⟨0,3,4⟩,
  ⟨1,2,3⟩,
  ⟨1,3,4⟩,
  ⟨2,3,5⟩
]

theorem checked : validate lines triangles 7 = true := by native_decide

theorem lower_bound : LowerBound 6 7 :=
  validate_sound lines triangles 7 checked

#print axioms checked
#print axioms lower_bound

end Kobon.Certificates.N006T00007H6ea9ebaa
