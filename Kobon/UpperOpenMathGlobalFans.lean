import Kobon.UpperOpenMathSupportedCores
import Kobon.UpperOpenMathCoreDoubleCount
import Kobon.UpperOpenMathMultiplicity
import Kobon.UpperOpenMathCoreHull

/-! Global budgets extracted from actual cyclic fans.  Every degree is
computed from the chosen certificate's real shared sides.  The local fan,
endpoint matching, global incidence sums, parity charges and core-line
budget are proved from geometry; no aggregate fan inequality is assumed. -/
namespace Kobon.UpperOpenMathGlobalFans
open Cells FanGeometry UpperVertexBudget UpperTriangleIncidence
  UpperSharedIncidence UpperEdgeInventory UpperCoreExtraction
  UpperCoreLineIncidence UpperOpenMathCoreDoubleCount
  UpperOpenMathActualFans UpperOpenMathSupportedCores Finset
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable def oneDegree {α : Type*} [Fintype α]
    (n : Nat) (L : Nat→Line ℝ) (geometry : α→TriangleGeometry) (p : Point) : Nat := by
  classical
  exact ((oneCoreEdges n L geometry).filter (fun e => p∈e)).card

noncomputable def twoDegree {α : Type*} [Fintype α]
    (n : Nat) (L : Nat→Line ℝ) (geometry : α→TriangleGeometry) (p : Point) : Nat := by
  classical
  exact ((twoCoreEdges n L geometry).filter (fun e => p∈e)).card

noncomputable def exceptionalCores {α : Type*} [Fintype α]
    (n : Nat) (L : Nat→Line ℝ) (geometry : α→TriangleGeometry) : Finset Point := by
  classical
  exact (core n L).filter (fun p => oneDegree n L geometry p=2*(supports n L p).card-3)

section Certificate
variable {α : Type*} [Fintype α]
  (n : Nat) (L : Nat→Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
  (tri : α→Triple) (hi : Function.Injective tri)
  (ht : ∀ a, TrianglePredicate n L (tri a))

include hn hi

theorem one_degree_sum :
    let G := fun a => ofPredicate n L (tri a) hL (ht a)
    (∑ p∈core n L, (oneDegree n L G p : ℤ))=(oneCoreEdges n L G).card := by
  dsimp only
  have h := one_core_incidence_sum n L hL tri hi ht
  dsimp only at h
  unfold oneDegree
  exact_mod_cast h

theorem two_degree_sum :
    let G := fun a => ofPredicate n L (tri a) hL (ht a)
    (∑ p∈core n L, (twoDegree n L G p : ℤ))=2*(twoCoreEdges n L G).card := by
  dsimp only
  have h := two_core_incidence_sum n L hL tri ht
  dsimp only at h
  unfold twoDegree
  exact_mod_cast h

theorem certificate_ordinary_fan_sum :
    let G := fun a => ofPredicate n L (tri a) hL (ht a)
    ((oneCoreEdges n L G).card : ℤ)≤
      2*(∑ p∈core n L, ((supports n L p).card : ℤ))-3*(core n L).card := by
  classical
  let G := fun a => ofPredicate n L (tri a) hL (ht a)
  have hp (p : Point) (hc : p∈core n L) :
      (oneDegree n L G p : ℤ)≤2*(supports n L p).card-3 := by
    have hr := core_multiplicity n L hL hc
    have hh := certificate_local_fan_bound n L hL hn tri hi ht p hc
    have hhZ : (oneDegree n L G p : ℤ)≤((2*(supports n L p).card-3 : Nat) : ℤ) := by
      exact_mod_cast hh
    simpa only [Nat.cast_sub (by omega : 3≤2*(supports n L p).card),
      Nat.cast_mul,Nat.cast_ofNat] using hhZ
  have hs := sum_le_sum (s:=core n L) hp
  rw [one_degree_sum n L hL hn tri hi ht] at hs
  simpa only [sum_sub_distrib,← mul_sum,sum_const,nsmul_eq_mul,mul_comm] using hs

theorem certificate_weighted_fan_sum :
    let G := fun a => ofPredicate n L (tri a) hL (ht a)
    3*((oneCoreEdges n L G).card : ℤ)+2*(twoCoreEdges n L G).card≤
      6*(∑ p∈core n L, ((supports n L p).card : ℤ))-8*(core n L).card+
        2*(exceptionalCores n L G).card := by
  classical
  let G := fun a => ofPredicate n L (tri a) hL (ht a)
  have hp (p : Point) (hc : p∈core n L) :
      3*(oneDegree n L G p : ℤ)+(twoDegree n L G p : ℤ)≤
        6*(supports n L p).card-8+
          (if oneDegree n L G p=2*(supports n L p).card-3 then 2 else 0 : ℤ) := by
    have hr := core_multiplicity n L hL hc
    have hh := certificate_local_weighted_bound n L hL hn tri hi ht p hc
    have hhZ : ((3*oneDegree n L G p+twoDegree n L G p : Nat) : ℤ)≤
      ((6*(supports n L p).card-8+
        (if oneDegree n L G p=2*(supports n L p).card-3 then 2 else 0) : Nat) : ℤ) := by
      exact_mod_cast hh
    have he : ((if oneDegree n L G p=2*(supports n L p).card-3 then 2 else 0 : Nat) : ℤ)=
      (if oneDegree n L G p=2*(supports n L p).card-3 then 2 else 0 : ℤ) := by
      split_ifs <;> norm_num
    simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,
      Nat.cast_sub (by omega : 8≤6*(supports n L p).card),he] using hhZ
  have hs := sum_le_sum (s:=core n L) hp
  have hE : (∑ p∈core n L,
      (if oneDegree n L G p=2*(supports n L p).card-3 then 2 else 0 : ℤ))=
      2*(exceptionalCores n L G).card := by
    simp [Finset.sum_ite,exceptionalCores,mul_comm]
  simp only [sum_add_distrib,sum_sub_distrib,← mul_sum,sum_const,nsmul_eq_mul,
    hE] at hs
  have h1 := one_degree_sum n L hL hn tri hi ht
  have h2 := two_degree_sum n L hL hn tri hi ht
  dsimp only at h1 h2
  rw [h1,h2] at hs
  dsimp only
  nlinarith [hs]

theorem exceptional_core_count :
    let G := fun a => ofPredicate n L (tri a) hL (ht a)
    (exceptionalCores n L G).card≤(core n L).card := by
  classical
  exact card_le_card (filter_subset _ _)

/-- At least three cores have a supporting line, unless fewer than three
cores exist. Every such core is nonextremal for the chosen triangle family. -/
theorem exceptional_boundary_budget :
    let G := fun a => ofPredicate n L (tri a) hL (ht a)
    (exceptionalCores n L G).card+min (core n L).card 3≤(core n L).card := by
  classical
  let G := fun a => ofPredicate n L (tri a) hL (ht a)
  let E := exceptionalCores n L G
  let B := UpperOpenMathCoreHull.boundary (core n L)
  have hdisj : Disjoint E B := by
    apply disjoint_left.mpr
    intro p he hb
    obtain ⟨hp,he⟩ := mem_filter.mp he
    obtain ⟨hpB,w,hw,valid,support⟩ := mem_filter.mp hb
    have hbound := certificate_supported_core_bound n L hL hn tri hi ht p hp w hw valid support
    have hr := core_multiplicity n L hL hp
    change oneDegree n L G p≤2*(supports n L p).card-4 at hbound
    change oneDegree n L G p=2*(supports n L p).card-3 at he
    rw [he] at hbound
    omega
  have hsub : E∪B⊆core n L := by
    intro p hp
    rcases mem_union.mp hp with hp|hp
    · exact (mem_filter.mp hp).1
    · exact (mem_filter.mp hp).1
  have hc := card_le_card hsub
  rw [card_union_of_disjoint hdisj] at hc
  have hb := UpperOpenMathCoreHull.boundary_card (core n L)
  dsimp [B,E,G] at hc
  dsimp only
  omega

/-- Every extremal fan consumes exactly three real core-to-core rays. -/
theorem exceptional_edge_budget :
    let G := fun a => ofPredicate n L (tri a) hL (ht a)
    3*((exceptionalCores n L G).card : ℤ)≤2*(twoCoreEdges n L G).card := by
  classical
  let G := fun a => ofPredicate n L (tri a) hL (ht a)
  have hp (p : Point) (hc : p∈core n L) :
      (if oneDegree n L G p=2*(supports n L p).card-3 then 3 else 0 : ℤ)≤
      (twoDegree n L G p : ℤ) := by
    split_ifs with he
    · have hh := certificate_extremal_neighbor_count n L hL hn tri hi ht p hc (le_of_eq he.symm)
      change twoDegree n L G p=3 at hh
      simp [hh]
    · positivity
  have hs := sum_le_sum (s:=core n L) hp
  have hE : (∑ p∈core n L,
      (if oneDegree n L G p=2*(supports n L p).card-3 then 3 else 0 : ℤ))=
      3*(exceptionalCores n L G).card := by
    simp [Finset.sum_ite,exceptionalCores,mul_comm]
  rw [hE,two_degree_sum n L hL hn tri hi ht] at hs
  exact hs

/-- A stronger arbitrary-order correction than endpoint capacity alone. -/
theorem certificate_defect_all :
    let G := fun a => ofPredicate n L (tri a) hL (ht a)
    2*(∑ p∈core n L, ((supports n L p).card : ℤ)*((supports n L p).card-4))+
      3*(core n L).card+UpperOpenMathCoreCapacity.nonsharedCoreIncidences n L G≤
      2*((n : ℤ)*(n-2)-3*Fintype.card α) := by
  classical
  let G := fun a => ofPredicate n L (tri a) hL (ht a)
  have hid := defect_identity n L hL hn tri hi ht
  have hf := certificate_ordinary_fan_sum n L hL hn tri hi ht
  have hc := UpperOpenMathCoreCapacity.certificate_capacity_with_nonshared n L hL hn tri hi ht
  have hcZ : ((oneCoreEdges n L G).card : ℤ)+2*(twoCoreEdges n L G).card+
      UpperOpenMathCoreCapacity.nonsharedCoreIncidences n L G≤
      2*(∑ p∈core n L, ((supports n L p).card : ℤ)) := by exact_mod_cast hc
  have hU : 0≤((edges n L\usedEdges G).card : ℤ) := by positivity
  dsimp only at hid hf ⊢
  rw [← UpperOpenMathMultiplicity.loss_minus_capacity_identity]
  linarith

end Certificate

section EvenCertificate
variable {α : Type*} [Fintype α]
  (n : Nat) (L : Nat→Line ℝ) (hL : NoParallel n L) (hn : 4≤n)
  (heven : n%2=0) (tri : α→Triple) (hi : Function.Injective tri)
  (ht : ∀ a, TrianglePredicate n L (tri a))

include hL hn heven tri hi ht

/-- The weighted deficit budget is now extracted from real geometry. -/
theorem certificate_defect_even :
    let G := fun a => ofPredicate n L (tri a) hL (ht a)
    (n : ℤ)+
      2*(∑ p∈core n L, (supports n L p).card*((supports n L p).card-2 : ℤ))-
      7*(∑ p∈core n L, ((supports n L p).card : ℤ))+8*(core n L).card+
      (twoCoreEdges n L G).card-2*(exceptionalCores n L G).card≤
      2*((n : ℤ)*(n-2)-3*Fintype.card α) := by
  classical
  let G := fun a => ofPredicate n L (tri a) hL (ht a)
  have hid := defect_identity n L hL (by omega) tri hi ht
  have hf := certificate_weighted_fan_sum n L hL (by omega) tri hi ht
  have hcore := core_line_budget n L hL (by omega) tri ht
  have hcharge := UpperCleanCharging.certificate_clean_line_budget n L hL (by omega) heven tri hi ht
  have hlines : (coreLines n L).card≤n := by
    have hh := card_le_card (subset_univ (coreLines n L))
    simpa only [card_univ,Fintype.card_fin] using hh
  have hcoreZ : ((twoCoreEdges n L G).card : ℤ)+(coreLines n L).card≤
      ∑ p∈core n L, ((supports n L p).card : ℤ) := by exact_mod_cast hcore
  have hchargeZ : (n : ℤ)-(coreLines n L).card≤
      2*(edges n L\usedEdges G).card+(oneCoreEdges n L G).card := by
    have hh : ((n-(coreLines n L).card : Nat) : ℤ)≤
      2*((edges n L\usedEdges G).card : ℤ)+(oneCoreEdges n L G).card := by exact_mod_cast hcharge
    simpa only [Nat.cast_sub hlines] using hh
  dsimp only at hid hf ⊢
  linarith

/-- Removing the exceptional-fan count still retains a stronger quadratic
multiplicity correction than the elementary endpoint-capacity estimate. -/
theorem certificate_fourfold_defect :
    2*(n : ℤ)+
      (∑ p∈core n L,
        (4*((supports n L p).card : ℤ)*((supports n L p).card-2)-
          14*(supports n L p).card+15))≤
      4*((n : ℤ)*(n-2)-3*Fintype.card α) := by
  classical
  let G := fun a => ofPredicate n L (tri a) hL (ht a)
  have hd := certificate_defect_even n L hL hn heven tri hi ht
  have he := exceptional_edge_budget n L hL (by omega) tri hi ht
  have hq := exceptional_core_count n L hL (by omega) tri hi ht
  have hqZ : ((exceptionalCores n L G).card : ℤ)≤(core n L).card := by exact_mod_cast hq
  dsimp only at hd he
  simp only [sum_add_distrib,sum_sub_distrib,← mul_sum,sum_const,nsmul_eq_mul]
  have hmul : (∑ p∈core n L,
      4*((supports n L p).card : ℤ)*((supports n L p).card-2))=
      4*(∑ p∈core n L, (supports n L p).card*((supports n L p).card-2 : ℤ)) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro p _
    ring
  rw [hmul]
  linarith

/-- Convex boundary geometry improves the multiplicity-only budget by up
to three further units, independently of the number of interior cores. -/
theorem certificate_fourfold_defect_boundary :
    2*(n : ℤ)+
      (∑ p∈core n L,
        (4*((supports n L p).card : ℤ)*((supports n L p).card-2)-
          14*(supports n L p).card+15))+(min (core n L).card 3 : Nat)≤
      4*((n : ℤ)*(n-2)-3*Fintype.card α) := by
  classical
  let G := fun a => ofPredicate n L (tri a) hL (ht a)
  have hd := certificate_defect_even n L hL hn heven tri hi ht
  have he := exceptional_edge_budget n L hL (by omega) tri hi ht
  have hq := exceptional_boundary_budget n L hL (by omega) tri hi ht
  have hqZ : ((exceptionalCores n L G).card : ℤ)+(min (core n L).card 3 : Nat)≤
      (core n L).card := by exact_mod_cast hq
  dsimp only at hd he
  simp only [sum_add_distrib,sum_sub_distrib,← mul_sum,sum_const,nsmul_eq_mul]
  have hmul : (∑ p∈core n L,
      4*((supports n L p).card : ℤ)*((supports n L p).card-2))=
      4*(∑ p∈core n L, (supports n L p).card*((supports n L p).card-2 : ℤ)) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro p _
    ring
  rw [hmul]
  linarith

/-- Every actual multiple point of multiplicity at least five forces an
additional correction beyond the even simple-arrangement polynomial. -/
theorem certificate_even_multiplicity_five
    (high : ∀ p∈core n L, 5≤(supports n L p).card) :
    12*(Fintype.card α : ℤ)+5*(core n L).card≤2*(n : ℤ)*(2*n-5) := by
  have hd := certificate_fourfold_defect n L hL hn heven tri hi ht
  have hp (p : Point) (hc : p∈core n L) : (5 : ℤ)≤
      4*((supports n L p).card : ℤ)*((supports n L p).card-2)-
        14*(supports n L p).card+15 := by
    have hr : (5 : ℤ)≤(supports n L p).card := by exact_mod_cast high p hc
    have hm := mul_nonneg (sub_nonneg.mpr hr)
      (by omega : (0 : ℤ)≤4*(supports n L p).card-2)
    nlinarith
  have hs := sum_le_sum (s:=core n L) hp
  simp only [sum_const,nsmul_eq_mul] at hs
  nlinarith

end EvenCertificate

#print axioms certificate_ordinary_fan_sum
#print axioms certificate_weighted_fan_sum
#print axioms exceptional_edge_budget
#print axioms exceptional_boundary_budget
#print axioms certificate_defect_all
#print axioms certificate_defect_even
#print axioms certificate_fourfold_defect
#print axioms certificate_fourfold_defect_boundary
#print axioms certificate_even_multiplicity_five
end Kobon.UpperOpenMathGlobalFans
