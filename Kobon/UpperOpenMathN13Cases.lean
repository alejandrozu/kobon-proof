import Kobon.UpperOpenMathOneCapThreeCore

namespace Kobon.UpperOpenMathN13Cases
open Finset
set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- A five-sector recipient is a unique four-shared-ray run. -/
theorem four_shared_run : ∀ T : Finset (ZMod 6),
    (T.filter (fun z=>z-1∈T)).card=4 →
    ∃ a : ZMod 6,
      T={a-1,a,a+1,a+2,a+3} ∧
      T.filter (fun z=>z-1∈T)={a,a+1,a+2,a+3} := by
  decide +kernel

/-- Exact finite classification before any geometric obstruction: two
    nonadjacent chosen core tips in the normalized recipient run leave
    precisely six positions for its lone ordinary tip. -/
theorem two_nonadjacent_core_positions : ∀ A : Finset (ZMod 6), ∀ o : ZMod 6,
    A⊆({0,1,2,3} : Finset (ZMod 6)) → A.card=2 →
    o∈({0,1,2,3} : Finset (ZMod 6)) → o∉A →
    (∀ z∈A, z+1∉A) →
      (A={0,2} ∧ (o=1∨o=3)) ∨
      (A={1,3} ∧ (o=0∨o=2)) ∨
      (A={0,3} ∧ (o=1∨o=2)) := by
  decide +kernel

#print axioms four_shared_run
#print axioms two_nonadjacent_core_positions
end Kobon.UpperOpenMathN13Cases

