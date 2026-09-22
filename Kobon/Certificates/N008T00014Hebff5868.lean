import Kobon.Geometry

namespace Kobon.Certificates.N008T00014Hebff5868

set_option maxRecDepth 100000
set_option maxHeartbeats 0

def lines : Array (Line ℤ) := #[
  ⟨0,6739,-4902⟩,
  ⟨1,2,-27⟩,
  ⟨20217,13478,152180⟩,
  ⟨47173,13478,40867⟩,
  ⟨17,-2,277⟩,
  ⟨26956,-13478,153053⟩,
  ⟨13478,-13478,117795⟩,
  ⟨1,-2,-11⟩
]

def triangles : List Triple := [
  ⟨0,1,7⟩,
  ⟨0,2,5⟩,
  ⟨0,2,6⟩,
  ⟨0,3,5⟩,
  ⟨0,3,7⟩,
  ⟨0,4,6⟩,
  ⟨1,2,4⟩,
  ⟨1,3,4⟩,
  ⟨1,5,6⟩,
  ⟨2,3,7⟩,
  ⟨2,5,7⟩,
  ⟨3,5,6⟩,
  ⟨4,5,7⟩,
  ⟨4,6,7⟩
]

theorem checked : validate lines triangles 14 = true := by native_decide

theorem lower_bound : LowerBound 8 14 :=
  validate_sound lines triangles 14 checked

#print axioms checked
#print axioms lower_bound

end Kobon.Certificates.N008T00014Hebff5868
