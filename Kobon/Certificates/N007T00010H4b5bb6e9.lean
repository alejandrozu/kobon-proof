import Kobon.Geometry

namespace Kobon.Certificates.N007T00010H4b5bb6e9

set_option maxRecDepth 100000
set_option maxHeartbeats 0

def lines : Array (Line ℤ) := #[
  ⟨0,1,0⟩,
  ⟨1,-1,-1⟩,
  ⟨2,-1,-4⟩,
  ⟨3,-1,-9⟩,
  ⟨7,-6,-15⟩,
  ⟨28,-19,2⟩,
  ⟨12,-5,-80⟩
]

def triangles : List Triple := [
  ⟨0,1,2⟩,
  ⟨0,1,5⟩,
  ⟨0,2,4⟩,
  ⟨0,3,4⟩,
  ⟨0,3,6⟩,
  ⟨1,2,3⟩,
  ⟨1,3,4⟩,
  ⟨1,4,6⟩,
  ⟨2,3,5⟩,
  ⟨2,5,6⟩
]

theorem checked : validate lines triangles 10 = true := by native_decide

theorem lower_bound : LowerBound 7 10 :=
  validate_sound lines triangles 10 checked

#print axioms checked
#print axioms lower_bound

end Kobon.Certificates.N007T00010H4b5bb6e9
