import Kobon.BoundaryExtension

/-! Finite sector-profile arithmetic for the exact 49-line successor experiment.
The map from these arrays to the real arrangements is independently computed
by audit_successor_chain.py; it is not an additional premise hidden in Lean. -/
namespace Kobon.Iteration49
open KobonBoundary
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def boundary_49 : Finset (ZMod 98) := {49,97,71,23,73,25,75,19,67,69,77,29,79,13,61,15,63,17,65,83,35,81,33,31,85,1,3,51,5,53,7,55,9,57,11,59,95,47,93,45,91,43,89,41,87,39,37}

theorem profile_bound_49 : ∀ j : ZMod 98, capCount 48 boundary_49 j ≤ 24 := by
  decide +kernel

theorem profile_attains_49 : capCount 48 boundary_49 28=24 := by
  decide +kernel

def boundary_50 : Finset (ZMod 100) := {99,23,25,19,29,78,81,13,15,17,85,83,87,1,3,5,7,9,11,97,95,93,91,89}

theorem profile_bound_50 : ∀ j : ZMod 100, capCount 49 boundary_50 j ≤ 23 := by
  decide +kernel

theorem profile_attains_50 : capCount 49 boundary_50 77=23 := by
  decide +kernel

def boundary_51 : Finset (ZMod 102) := {78,26,30}

theorem profile_bound_51 : ∀ j : ZMod 102, capCount 50 boundary_51 j ≤ 2 := by
  decide +kernel

theorem profile_attains_51 : capCount 50 boundary_51 0=2 := by
  decide +kernel

def boundary_52 : Finset (ZMod 104) := {79,97,44}

theorem profile_bound_52 : ∀ j : ZMod 104, capCount 51 boundary_52 j ≤ 2 := by
  decide +kernel

theorem profile_attains_52 : capCount 51 boundary_52 29=2 := by
  decide +kernel

def boundary_53 : Finset (ZMod 106) := {31,99,83}

theorem profile_bound_53 : ∀ j : ZMod 106, capCount 52 boundary_53 j ≤ 2 := by
  decide +kernel

theorem profile_attains_53 : capCount 52 boundary_53 48=2 := by
  decide +kernel

#print axioms profile_bound_50
#print axioms profile_attains_50
end Kobon.Iteration49
