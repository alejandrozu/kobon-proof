import Kobon.Geometry

namespace Kobon.Certificates.N008T00014H2a63f4d9

set_option maxRecDepth 100000
set_option maxHeartbeats 0

def lines : Array (Line ℤ) := #[
  ⟨3901806440322565,19615705608064608,11111404660392044⟩,
  ⟨2777851165098011,4157348061512726,4903926402016152⟩,
  ⟨8314696123025452,5555702330196023,1950903220161286⟩,
  ⟨98078528040323040,19509032201612833,-83146961230254520⟩,
  ⟨9807852804032304,-1950903220161282,-8314696123025455⟩,
  ⟨41573480615127265,-27778511650980100,9754516100806368⟩,
  ⟨5555702330196022,-8314696123025453,9807852804032305⟩,
  ⟨975451610080643,-4903926402016152,2777851165098019⟩
]

def triangles : List Triple := [
  ⟨0,1,5⟩,
  ⟨0,1,6⟩,
  ⟨0,2,4⟩,
  ⟨0,2,5⟩,
  ⟨0,3,4⟩,
  ⟨1,2,3⟩,
  ⟨1,2,4⟩,
  ⟨1,6,7⟩,
  ⟨2,5,7⟩,
  ⟨2,6,7⟩,
  ⟨3,4,7⟩,
  ⟨3,5,6⟩,
  ⟨3,5,7⟩,
  ⟨4,5,6⟩
]

theorem checked : validate lines triangles 14 = true := by native_decide

theorem lower_bound : LowerBound 8 14 :=
  validate_sound lines triangles 14 checked

#print axioms checked
#print axioms lower_bound

end Kobon.Certificates.N008T00014H2a63f4d9
