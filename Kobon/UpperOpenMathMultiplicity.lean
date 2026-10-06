import Kobon.UpperOpenMathCoreCapacity
import Kobon.UpperCleanCharging

/-!
# Fully extracted multiplicity-sensitive upper bounds

All numerical counts in the final statements come from actual finite
nonparallel real-line arrangements and actual injective lists of certified
triangles. The capacity theorem eliminates an aggregate fan assumption.

At even order, the resulting defect estimate is
`2*delta >= n + sum r*(2*r-11) + 5*D2`.
At arbitrary order it is
`delta >= sum r*(r-4) + D2`.
Consequently arrangements whose multiple points all have multiplicity at
least six satisfy the classical even simple-arrangement bound, with an
additional nonnegative correction. This is a restricted structural result;
triple, quadruple and quintuple points remain explicitly penalized in the
general formula.
-/
namespace Kobon.UpperOpenMathMultiplicity
open Cells FanGeometry UpperVertexBudget UpperTriangleIncidence
  UpperSharedIncidence UpperEdgeInventory UpperCoreExtraction
  UpperCoreLineIncidence Finset
open scoped BigOperators

theorem core_weight_identity (n : ℕ) (L : ℕ → Line ℝ) :
    2*(∑ p∈core n L, (supports n L p).card*((supports n L p).card-2 : ℤ))-
      7*(∑ p∈core n L, ((supports n L p).card : ℤ))=
    ∑ p∈core n L, ((supports n L p).card : ℤ)*(2*(supports n L p).card-11) := by
  rw [mul_sum,mul_sum,← sum_sub_distrib]
  apply sum_congr rfl
  intro p _
  ring

theorem loss_minus_capacity_identity (n : ℕ) (L : ℕ → Line ℝ) :
    (∑ p∈core n L, (supports n L p).card*((supports n L p).card-2 : ℤ))-
      2*(∑ p∈core n L, ((supports n L p).card : ℤ))=
    ∑ p∈core n L, ((supports n L p).card : ℤ)*((supports n L p).card-4) := by
  rw [mul_sum,← sum_sub_distrib]
  apply sum_congr rfl
  intro p _
  ring

/-- Arbitrary-order geometric defect bound. No local fan or aggregate
incidence assumption is supplied by the caller. -/
theorem certificate_defect_all {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a)) :
    let geometry := fun a => ofPredicate n L (tri a) hL (ht a)
    (∑ p∈core n L, ((supports n L p).card : ℤ)*((supports n L p).card-4))+
      (twoCoreEdges n L geometry).card≤
      (n : ℤ)*(n-2)-3*Fintype.card α := by
  classical
  let geometry := fun a => ofPredicate n L (tri a) hL (ht a)
  have hid := defect_identity n L hL hn tri hi ht
  have hc := UpperOpenMathCoreCapacity.certificate_shared_core_capacity n L hL hn tri hi ht
  have hcZ : ((oneCoreEdges n L geometry).card : ℤ)+
      2*(twoCoreEdges n L geometry).card≤2*(∑ p∈core n L, ((supports n L p).card : ℤ)) := by
    exact_mod_cast hc
  have hU : 0≤((edges n L\usedEdges geometry).card : ℤ) := by positivity
  rw [← loss_minus_capacity_identity]
  dsimp only at hid
  linarith

/-- At even order all parity, endpoint-capacity and core-line budgets are
derived from actual geometry. The correction depends only on actual core
multiplicities and actual core-to-core shared edges. -/
theorem certificate_defect_even {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L)
    (hn : 4≤n) (heven : n%2=0)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a)) :
    let geometry := fun a => ofPredicate n L (tri a) hL (ht a)
    (n : ℤ)+
      (∑ p∈core n L, ((supports n L p).card : ℤ)*(2*(supports n L p).card-11))+
      5*(twoCoreEdges n L geometry).card≤
      2*((n : ℤ)*(n-2)-3*Fintype.card α) := by
  classical
  let geometry := fun a => ofPredicate n L (tri a) hL (ht a)
  have hid := defect_identity n L hL (by omega) tri hi ht
  have hc := UpperOpenMathCoreCapacity.certificate_shared_core_capacity n L hL (by omega) tri hi ht
  have hcore := core_line_budget n L hL (by omega) tri ht
  have hcharge := UpperCleanCharging.certificate_clean_line_budget n L hL (by omega) heven tri hi ht
  have hlines : (coreLines n L).card≤n := by
    have hh := card_le_card (subset_univ (coreLines n L))
    simpa only [card_univ,Fintype.card_fin] using hh
  have hcZ : ((oneCoreEdges n L geometry).card : ℤ)+
      2*(twoCoreEdges n L geometry).card≤2*(∑ p∈core n L, ((supports n L p).card : ℤ)) := by
    exact_mod_cast hc
  have hcoreZ : ((twoCoreEdges n L geometry).card : ℤ)+(coreLines n L).card≤
      ∑ p∈core n L, ((supports n L p).card : ℤ) := by
    exact_mod_cast hcore
  have hchargeZ : (n : ℤ)-(coreLines n L).card≤
      2*(edges n L\usedEdges geometry).card+(oneCoreEdges n L geometry).card := by
    have hh : ((n-(coreLines n L).card : ℕ) : ℤ)≤
        2*((edges n L\usedEdges geometry).card : ℤ)+(oneCoreEdges n L geometry).card := by
      exact_mod_cast hcharge
    simpa only [Nat.cast_sub hlines] using hh
  rw [← core_weight_identity]
  dsimp only at hid
  linarith

theorem high_core_weight (n : ℕ) (L : ℕ → Line ℝ)
    (high : ∀ p∈core n L, 6≤(supports n L p).card) :
    6*(core n L).card≤
      ∑ p∈core n L, ((supports n L p).card : ℤ)*(2*(supports n L p).card-11) := by
  have hp (p : Point) (h : p∈core n L) :
      (6 : ℤ)≤((supports n L p).card : ℤ)*(2*(supports n L p).card-11) := by
    have hr : (6 : ℤ)≤(supports n L p).card := by exact_mod_cast high p h
    have hp := mul_nonneg (sub_nonneg.mpr hr) (by omega : (0 : ℤ)≤2*(supports n L p).card+1)
    nlinarith
  have hh := sum_le_sum (s:=core n L) hp
  simpa only [sum_const,nsmul_eq_mul,mul_comm] using hh

theorem certificate_defect_all_with_nonshared {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a)) :
    let geometry := fun a => ofPredicate n L (tri a) hL (ht a)
    (∑ p∈core n L, ((supports n L p).card : ℤ)*((supports n L p).card-4))+
      (twoCoreEdges n L geometry).card+
      UpperOpenMathCoreCapacity.nonsharedCoreIncidences n L geometry≤
      (n : ℤ)*(n-2)-3*Fintype.card α := by
  classical
  let geometry := fun a => ofPredicate n L (tri a) hL (ht a)
  have hid := defect_identity n L hL hn tri hi ht
  have hc := UpperOpenMathCoreCapacity.certificate_capacity_with_nonshared n L hL hn tri hi ht
  have hcZ : ((oneCoreEdges n L geometry).card : ℤ)+
      2*(twoCoreEdges n L geometry).card+
      UpperOpenMathCoreCapacity.nonsharedCoreIncidences n L geometry≤
      2*(∑ p∈core n L, ((supports n L p).card : ℤ)) := by
    exact_mod_cast hc
  have hU : 0≤((edges n L\usedEdges geometry).card : ℤ) := by positivity
  rw [← loss_minus_capacity_identity]
  dsimp only at hid
  linarith

/-- Three times the actual nonshared core-endpoint count improves the even
defect budget. This retains real unused/single-edge geometry that disappears
from the simpler multiplicity-only bound. -/
theorem certificate_defect_even_with_nonshared {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L)
    (hn : 4≤n) (heven : n%2=0)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a)) :
    let geometry := fun a => ofPredicate n L (tri a) hL (ht a)
    (n : ℤ)+
      (∑ p∈core n L, ((supports n L p).card : ℤ)*(2*(supports n L p).card-11))+
      5*(twoCoreEdges n L geometry).card+
      3*UpperOpenMathCoreCapacity.nonsharedCoreIncidences n L geometry≤
      2*((n : ℤ)*(n-2)-3*Fintype.card α) := by
  classical
  let geometry := fun a => ofPredicate n L (tri a) hL (ht a)
  have hid := defect_identity n L hL (by omega) tri hi ht
  have hc := UpperOpenMathCoreCapacity.certificate_capacity_with_nonshared n L hL (by omega) tri hi ht
  have hcore := core_line_budget n L hL (by omega) tri ht
  have hcharge := UpperCleanCharging.certificate_clean_line_budget n L hL (by omega) heven tri hi ht
  have hlines : (coreLines n L).card≤n := by
    have hh := card_le_card (subset_univ (coreLines n L))
    simpa only [card_univ,Fintype.card_fin] using hh
  have hcZ : ((oneCoreEdges n L geometry).card : ℤ)+
      2*(twoCoreEdges n L geometry).card+
      UpperOpenMathCoreCapacity.nonsharedCoreIncidences n L geometry≤
      2*(∑ p∈core n L, ((supports n L p).card : ℤ)) := by
    exact_mod_cast hc
  have hcoreZ : ((twoCoreEdges n L geometry).card : ℤ)+(coreLines n L).card≤
      ∑ p∈core n L, ((supports n L p).card : ℤ) := by
    exact_mod_cast hcore
  have hchargeZ : (n : ℤ)-(coreLines n L).card≤
      2*(edges n L\usedEdges geometry).card+(oneCoreEdges n L geometry).card := by
    have hh : ((n-(coreLines n L).card : ℕ) : ℤ)≤
        2*((edges n L\usedEdges geometry).card : ℤ)+(oneCoreEdges n L geometry).card := by
      exact_mod_cast hcharge
    simpa only [Nat.cast_sub hlines] using hh
  rw [← core_weight_identity]
  dsimp only at hid
  linarith

/-- Broad nonsimple class: when all multiple points have multiplicity at
least six, the even simple-arrangement upper polynomial remains valid and
loses at least one additional triangle per actual multiple point. -/
theorem certificate_even_high_multiplicity {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L)
    (hn : 4≤n) (heven : n%2=0)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (high : ∀ p∈core n L, 6≤(supports n L p).card) :
    6*(Fintype.card α : ℤ)+6*(core n L).card≤(n : ℤ)*(2*n-5) := by
  have h := certificate_defect_even n L hL hn heven tri hi ht
  have hw := high_core_weight n L high
  have hz : 0≤((twoCoreEdges n L (fun a => ofPredicate n L (tri a) hL (ht a))).card : ℤ) := by positivity
  dsimp only at h
  nlinarith

/-- At arbitrary order, multiplicities at least four are already enough
for the classical simple bound; each higher multiplicity contributes its
full quadratic correction and shared core edges further decrease it. -/
theorem certificate_all_high_multiplicity {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (high : ∀ p∈core n L, 4≤(supports n L p).card) :
    3*(Fintype.card α : ℤ)≤(n : ℤ)*(n-2) := by
  have h := certificate_defect_all n L hL hn tri hi ht
  have hw : 0≤∑ p∈core n L, ((supports n L p).card : ℤ)*((supports n L p).card-4) := by
    apply sum_nonneg
    intro p hp
    apply mul_nonneg (by positivity)
    have hh : (4 : ℤ)≤(supports n L p).card := by exact_mod_cast high p hp
    omega
  have hz : 0≤((twoCoreEdges n L (fun a => ofPredicate n L (tri a) hL (ht a))).card : ℤ) := by positivity
  dsimp only at h
  linarith

#print axioms certificate_defect_all
#print axioms certificate_defect_even
#print axioms certificate_defect_all_with_nonshared
#print axioms certificate_defect_even_with_nonshared
#print axioms certificate_even_high_multiplicity
#print axioms certificate_all_high_multiplicity
end Kobon.UpperOpenMathMultiplicity
