import Kobon.SharedFan
import Kobon.CleanLineBudget
import Kobon.FanGeometry
import Kobon.FanCount
import Kobon.CyclicFan

/-! Reproduce with `lake env lean experiments/2026-09-21/general-bounds/audit_general_bounds.lean`.
This audits the proof dependencies, not the unfinished global geometric premises. -/

#print axioms Kobon.SharedFan.six_shared_sides
#print axioms Kobon.SharedFan.radial_segments_injective
#print axioms Kobon.SharedFan.radial_elementary
#print axioms Kobon.SharedFan.interiors_disjoint
#print axioms Kobon.FanGeometry.no_opposite_end_fan
#print axioms Kobon.FanCount.ordinary_shared_ray_bound
#print axioms Kobon.CyclicFan.Geometry.no_long_run
#print axioms Kobon.CyclicFan.Geometry.selected_card_le
#print axioms Kobon.CleanLineBudget.parity_budget
#print axioms Kobon.CleanLineBudget.at_most_two_triple_points
#print axioms Kobon.CleanLineBudget.one_triple_point
#print axioms Kobon.CleanLineBudget.multiplicity_surplus
#print axioms Kobon.CleanLineBudget.at_most_two_multiple_points
#print axioms Kobon.CleanLineBudget.general_multiplicity_budget
#print axioms Kobon.CleanLineBudget.high_multiplicity_weight
#print axioms Kobon.CleanLineBudget.nonnegative_core_weight
#print axioms Kobon.CleanLineBudget.triangles_from_defect
