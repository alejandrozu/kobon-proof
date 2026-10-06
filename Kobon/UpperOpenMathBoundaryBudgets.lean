import Kobon.UpperOpenMathGlobalFans

/-! Boundary-sensitive budgets for actual certificates.  A supporting
multiple point is nonextremal, so the full size of the convex boundary,
not just its three-point lower bound, contributes to the deficit. -/
namespace Kobon.UpperOpenMathBoundaryBudgets
open Cells FanGeometry UpperVertexBudget UpperTriangleIncidence
  UpperSharedIncidence UpperEdgeInventory UpperCoreExtraction
  UpperCoreLineIncidence UpperCoreCombinatorics UpperOpenMathGlobalFans
  UpperOpenMathSupportedCores UpperOpenMathActualFans Finset
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1000000

section Certificate
variable {α : Type*} [Fintype α]
  (n : Nat) (L : Nat→Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
  (tri : α→Triple) (hi : Function.Injective tri)
  (ht : ∀ a, TrianglePredicate n L (tri a))
include hn hi

theorem certificate_boundary_fan_sum :
    let G := fun a => ofPredicate n L (tri a) hL (ht a)
    ((oneCoreEdges n L G).card : ℤ)≤
      2*(∑ p∈core n L, ((supports n L p).card : ℤ))-3*(core n L).card-
        (UpperOpenMathCoreHull.boundary (core n L)).card := by
  classical
  let G := fun a => ofPredicate n L (tri a) hL (ht a)
  have hp (p : Point) (hc : p∈core n L) :
      (oneDegree n L G p : ℤ)≤2*(supports n L p).card-3-
        (if UpperOpenMathCoreHull.HasSupport (core n L) p then 1 else 0 : ℤ) := by
    have hr := core_multiplicity n L hL hc
    by_cases hb : UpperOpenMathCoreHull.HasSupport (core n L) p
    · have hbs := hb
      obtain ⟨w,hw,valid,support⟩ := hb
      have hh := certificate_supported_core_bound n L hL hn tri hi ht p hc w hw valid support
      change oneDegree n L G p≤2*(supports n L p).card-4 at hh
      have hz : (oneDegree n L G p : ℤ)≤((2*(supports n L p).card-4 : Nat) : ℤ) := by exact_mod_cast hh
      simp only [Nat.cast_sub (by omega : 4≤2*(supports n L p).card),Nat.cast_mul,Nat.cast_ofNat] at hz
      simp only [if_pos hbs]
      linarith
    · have hh := certificate_local_fan_bound n L hL hn tri hi ht p hc
      change oneDegree n L G p≤2*(supports n L p).card-3 at hh
      have hz : (oneDegree n L G p : ℤ)≤((2*(supports n L p).card-3 : Nat) : ℤ) := by exact_mod_cast hh
      simp only [Nat.cast_sub (by omega : 3≤2*(supports n L p).card),Nat.cast_mul,Nat.cast_ofNat] at hz
      simpa only [if_neg hb,sub_zero] using hz
  have hs := sum_le_sum (s:=core n L) hp
  have hB : (∑ p∈core n L,
      (if UpperOpenMathCoreHull.HasSupport (core n L) p then 1 else 0 : ℤ))=
      (UpperOpenMathCoreHull.boundary (core n L)).card := by
    simp [Finset.sum_ite,UpperOpenMathCoreHull.boundary]
  have h1 := one_degree_sum n L hL hn tri hi ht
  dsimp only at h1
  simp only [sum_sub_distrib,← mul_sum,sum_const,nsmul_eq_mul,hB] at hs
  rw [h1] at hs
  dsimp only
  linarith

/-- The arbitrary-order correction retains all supporting core points. -/
theorem certificate_boundary_defect_all :
    let G := fun a => ofPredicate n L (tri a) hL (ht a)
    2*(∑ p∈core n L, ((supports n L p).card : ℤ)*((supports n L p).card-4))+
      3*(core n L).card+UpperOpenMathCoreCapacity.nonsharedCoreIncidences n L G+
      (UpperOpenMathCoreHull.boundary (core n L)).card≤
      2*((n : ℤ)*(n-2)-3*Fintype.card α) := by
  classical
  let G := fun a => ofPredicate n L (tri a) hL (ht a)
  have hid := defect_identity n L hL hn tri hi ht
  have hf := certificate_boundary_fan_sum n L hL hn tri hi ht
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

theorem certificate_boundary_defect_even :
    let G := fun a => ofPredicate n L (tri a) hL (ht a)
    (n : ℤ)+
      2*(∑ p∈core n L, (supports n L p).card*((supports n L p).card-2 : ℤ))-
      7*(∑ p∈core n L, ((supports n L p).card : ℤ))+9*(core n L).card+
      3*(UpperOpenMathCoreHull.boundary (core n L)).card-(twoCoreEdges n L G).card≤
      2*((n : ℤ)*(n-2)-3*Fintype.card α) := by
  classical
  let G := fun a => ofPredicate n L (tri a) hL (ht a)
  have hid := defect_identity n L hL (by omega) tri hi ht
  have hf := certificate_boundary_fan_sum n L hL (by omega) tri hi ht
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

/-- Few multiple points: all convex-boundary, local and line-path budgets
are derived from the input geometry. No aggregate premise remains. -/
theorem certificate_three_core_defect (small : (core n L).card≤3) :
    let G := fun a => ofPredicate n L (tri a) hL (ht a)
    (n : ℤ)-3*(core n L).card-(twoCoreEdges n L G).card≤
      2*((n : ℤ)*(n-2)-3*Fintype.card α) := by
  have hd := certificate_boundary_defect_even n L hL hn heven tri hi ht
  have hs := core_surplus n L hL
  have hb := UpperOpenMathCoreHull.boundary_card (core n L)
  rw [Nat.min_eq_left small] at hb
  have hbZ : ((core n L).card : ℤ)≤(UpperOpenMathCoreHull.boundary (core n L)).card := by exact_mod_cast hb
  dsimp only at hd ⊢
  linarith

theorem certificate_three_core_upper (small : (core n L).card≤3) :
    6*(Fintype.card α : ℤ)≤(n : ℤ)*(2*n-5)+12 := by
  have hd := certificate_three_core_defect n L hL hn heven tri hi ht small
  have he := three_core_edge_count n L hL tri ht small
  have heZ : ((twoCoreEdges n L (fun a => ofPredicate n L (tri a) hL (ht a))).card : ℤ)≤3 := by exact_mod_cast he
  have hs : ((core n L).card : ℤ)≤3 := by exact_mod_cast small
  dsimp only at hd
  nlinarith

theorem certificate_two_core_upper (small : (core n L).card≤2) :
    6*(Fintype.card α : ℤ)≤(n : ℤ)*(2*n-5)+6 := by
  have hd := certificate_three_core_defect n L hL hn heven tri hi ht (by omega)
  have he := core_edge_count n L hL tri ht
  have hchoose := Nat.choose_le_choose 2 small
  norm_num at hchoose
  have heZ : ((twoCoreEdges n L (fun a => ofPredicate n L (tri a) hL (ht a))).card : ℤ)≤1 := by
    have hh : (twoCoreEdges n L (fun a => ofPredicate n L (tri a) hL (ht a))).card≤1 := by omega
    exact_mod_cast hh
  have hs : ((core n L).card : ℤ)≤2 := by exact_mod_cast small
  have hn2 : (n : ℤ)=2*(n/2 : Nat) := by omega
  let δ : ℤ := (n : ℤ)*(n-2)-3*Fintype.card α
  have hδ : (n : ℤ)-7≤2*δ := by dsimp [δ]; dsimp only at hd; linarith
  have hδ2 : (n : ℤ)-6≤2*δ := by omega
  dsimp [δ] at hδ2
  nlinarith

/-- Multiplicity at least five gives a strictly penalized even bound,
with the convex boundary supplying an additional correction. -/
theorem certificate_even_high_five
    (high : ∀ p∈core n L, 5≤(supports n L p).card) :
    12*(Fintype.card α : ℤ)+5*(core n L).card+(min (core n L).card 3 : Nat)≤
      2*(n : ℤ)*(2*n-5) := by
  have hd := certificate_fourfold_defect_boundary n L hL hn heven tri hi ht
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
#print axioms certificate_boundary_fan_sum
#print axioms certificate_boundary_defect_all
#print axioms certificate_boundary_defect_even
#print axioms certificate_three_core_upper
#print axioms certificate_two_core_upper
#print axioms certificate_even_high_five
end Kobon.UpperOpenMathBoundaryBudgets
