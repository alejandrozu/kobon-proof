import Kobon.Geometry

namespace Kobon.Certificates.N009T00021H6ebbed82

set_option maxRecDepth 100000
set_option maxHeartbeats 0

def lines : Array (Line ℤ) := #[
  ⟨2,6,33⟩,
  ⟨2,3,-21⟩,
  ⟨4,3,-12⟩,
  ⟨6,2,-81⟩,
  ⟨98,-3,-303⟩,
  ⟨5,-2,-39⟩,
  ⟨2,-2,11⟩,
  ⟨1,-2,-10⟩,
  ⟨0,3,-7⟩
]

def triangles : List Triple := [
  ⟨0,1,3⟩,
  ⟨0,2,3⟩,
  ⟨0,2,5⟩,
  ⟨0,4,5⟩,
  ⟨0,4,7⟩,
  ⟨0,6,7⟩,
  ⟨0,6,8⟩,
  ⟨1,2,6⟩,
  ⟨1,3,7⟩,
  ⟨1,4,6⟩,
  ⟨1,4,8⟩,
  ⟨1,5,7⟩,
  ⟨1,5,8⟩,
  ⟨2,4,7⟩,
  ⟨2,4,8⟩,
  ⟨2,5,7⟩,
  ⟨2,6,8⟩,
  ⟨3,4,6⟩,
  ⟨3,5,6⟩,
  ⟨3,5,8⟩,
  ⟨3,7,8⟩
]

theorem checked : validate lines triangles 21 = true := by native_decide

theorem lower_bound : LowerBound 9 21 :=
  validate_sound lines triangles 21 checked

#print axioms checked
#print axioms lower_bound

end Kobon.Certificates.N009T00021H6ebbed82
