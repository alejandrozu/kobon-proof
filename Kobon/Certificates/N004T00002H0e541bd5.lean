import Kobon.Geometry

namespace Kobon.Certificates.N004T00002H0e541bd5

set_option maxRecDepth 100000
set_option maxHeartbeats 0

def lines : Array (Line ℤ) := #[
  ⟨1275611441216966,3079598441704289,3079598441704289⟩,
  ⟨92387953251128670,38268343236508984,-38268343236508967⟩,
  ⟨9238795325112867,-3826834323650897,-3826834323650904⟩,
  ⟨3826834323650899,-9238795325112867,9238795325112867⟩
]

def triangles : List Triple := [
  ⟨0,1,2⟩,
  ⟨1,2,3⟩
]

theorem checked : validate lines triangles 2 = true := by native_decide

theorem lower_bound : LowerBound 4 2 :=
  validate_sound lines triangles 2 checked

#print axioms checked
#print axioms lower_bound

end Kobon.Certificates.N004T00002H0e541bd5
