import Kobon.Geometry

namespace Kobon.Certificates.N007T00011He6b9a626

set_option maxRecDepth 100000
set_option maxHeartbeats 0

def lines : Array (Line ℤ) := #[
  ⟨1,3,18⟩,
  ⟨4,6,-51⟩,
  ⟨6,3,-97⟩,
  ⟨211,-3,-1721⟩,
  ⟨2,-1,7⟩,
  ⟨2,-3,-27⟩,
  ⟨2,-6,21⟩
]

def triangles : List Triple := [
  ⟨0,1,2⟩,
  ⟨0,3,5⟩,
  ⟨0,4,5⟩,
  ⟨0,4,6⟩,
  ⟨1,2,5⟩,
  ⟨1,3,5⟩,
  ⟨1,3,6⟩,
  ⟨1,4,6⟩,
  ⟨2,3,4⟩,
  ⟨2,3,6⟩,
  ⟨2,5,6⟩
]

theorem checked : validate lines triangles 11 = true := by native_decide

theorem lower_bound : LowerBound 7 11 :=
  validate_sound lines triangles 11 checked

#print axioms checked
#print axioms lower_bound

end Kobon.Certificates.N007T00011He6b9a626
