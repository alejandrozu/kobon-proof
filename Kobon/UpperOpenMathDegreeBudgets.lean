import Kobon.UpperOpenMathGlobalFans
import Kobon.UpperSimpleOptimality

/-! Graph-degree refinements for actual shared core sides.
The graph property is stated directly on the real certificate's edges.
It does not assume a local fan, incidence identity, or aggregate inequality. -/
namespace Kobon.UpperOpenMathDegreeBudgets
open Cells FanGeometry UpperVertexBudget UpperTriangleIncidence
  UpperSharedIncidence UpperEdgeInventory UpperCoreExtraction
  UpperOpenMathRadialOrder UpperOpenMathActualFans UpperOpenMathGlobalFans Finset
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1000000

section Certificate
variable {α : Type*} [Fintype α]
  (n : Nat) (L : Nat→Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
  (tri : α→Triple) (hi : Function.Injective tri)
  (ht : ∀ a, TrianglePredicate n L (tri a))
include hn hi

theorem certificate_local_degree_two (c : Point) (hcore : c∈core n L)
    (degree : twoDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) c≤2) :
    oneDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) c≤
      2*(supports n L c).card-4 := by
  classical
  have hr := core_multiplicity n L hL hcore
  letI : NeZero (2*(supports n L c).card) := ⟨by omega⟩
  let D := atPoint n L hL hn c
  have hc := (mem_filter.mp hcore).1
  unfold oneDegree
  rw [← fan_ordinary_card n L hL hn tri ht c hc D (by omega) hi hcore]
  apply (fan n L hL hn tri ht c hc D (by omega)).ordinary_shared_card_le_of_core_le_two hr
  rw [fan_core_card n L hL hn tri ht c hc D (by omega) hi hcore]
  exact degree

theorem certificate_degree_two_fan_sum
    (degree : ∀ p∈core n L,
      twoDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) p≤2) :
    let G := fun a => ofPredicate n L (tri a) hL (ht a)
    ((oneCoreEdges n L G).card : ℤ)≤
      2*(∑ p∈core n L, ((supports n L p).card : ℤ))-4*(core n L).card := by
  classical
  let G := fun a => ofPredicate n L (tri a) hL (ht a)
  have hp (p : Point) (hc : p∈core n L) :
      (oneDegree n L G p : ℤ)≤2*(supports n L p).card-4 := by
    have hr := core_multiplicity n L hL hc
    have hh := certificate_local_degree_two n L hL hn tri hi ht p hc (degree p hc)
    have hz : (oneDegree n L G p : ℤ)≤((2*(supports n L p).card-4 : Nat) : ℤ) := by exact_mod_cast hh
    simpa only [Nat.cast_sub (by omega : 4≤2*(supports n L p).card),Nat.cast_mul,Nat.cast_ofNat] using hz
  have hs := sum_le_sum (s:=core n L) hp
  have h1 := one_degree_sum n L hL hn tri hi ht
  dsimp only at h1
  rw [h1] at hs
  dsimp only
  simpa only [sum_sub_distrib,← mul_sum,sum_const,nsmul_eq_mul,mul_comm] using hs

omit hn hi in
theorem square_loss_identity :
    (∑ p∈core n L, (supports n L p).card*((supports n L p).card-2 : ℤ))-
      2*(∑ p∈core n L, ((supports n L p).card : ℤ))+4*(core n L).card=
    ∑ p∈core n L, (((supports n L p).card : ℤ)-2)^2 := by
  have hC : 4*((core n L).card : ℤ)=(∑ p∈core n L, (4 : ℤ)) := by simp [sum_const,nsmul_eq_mul,mul_comm]
  rw [mul_sum,← sum_sub_distrib,hC,← sum_add_distrib]
  apply sum_congr rfl
  intro p _
  ring

/-- Each actual core contributes its squared multiplicity loss when its
shared core degree is at most two. Unused edges and shared core edges
are retained separately. -/
theorem certificate_degree_two_square_defect
    (degree : ∀ p∈core n L,
      twoDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) p≤2) :
    let G := fun a => ofPredicate n L (tri a) hL (ht a)
    (∑ p∈core n L, (((supports n L p).card : ℤ)-2)^2)+
      (edges n L\usedEdges G).card-(twoCoreEdges n L G).card≤
      (n : ℤ)*(n-2)-3*Fintype.card α := by
  have hid := defect_identity n L hL hn tri hi ht
  have hf := certificate_degree_two_fan_sum n L hL hn tri hi ht degree
  dsimp only at hid hf ⊢
  rw [← square_loss_identity n L]
  linarith

/-- Raj's general-position squared-loss mechanism extends to every actual
certificate with no shared core-to-core side, even if some arrangement
line passes through several cores. -/
theorem certificate_no_core_sides
    (empty : twoCoreEdges n L (fun a => ofPredicate n L (tri a) hL (ht a))=∅) :
    let G := fun a => ofPredicate n L (tri a) hL (ht a)
    (∑ p∈core n L, (((supports n L p).card : ℤ)-2)^2)+
      (edges n L\usedEdges G).card≤
      (n : ℤ)*(n-2)-3*Fintype.card α := by
  have degree (p : Point) (_ : p∈core n L) :
      twoDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) p≤2 := by
    simp [twoDegree,empty]
  have h := certificate_degree_two_square_defect n L hL hn tri hi ht degree
  simpa only [empty,card_empty,Nat.cast_zero,sub_zero] using h

/-- A zero-defect certificate with shared core degree at most two must
have at least as many core sides as core points. Hence a nonempty core
cannot have a forest with fewer than q edges. -/
theorem perfect_requires_core_cycle_count
    (degree : ∀ p∈core n L,
      twoDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) p≤2)
    (perfect : (n : ℤ)*(n-2)=3*Fintype.card α) :
    let G := fun a => ofPredicate n L (tri a) hL (ht a)
    (core n L).card≤(twoCoreEdges n L G).card := by
  have hd := certificate_degree_two_square_defect n L hL hn tri hi ht degree
  have hp (p : Point) (hc : p∈core n L) : (1 : ℤ)≤(((supports n L p).card : ℤ)-2)^2 := by
    have hr : (3 : ℤ)≤(supports n L p).card := by exact_mod_cast core_multiplicity n L hL hc
    nlinarith [sq_nonneg (((supports n L p).card : ℤ)-3)]
  have hs := sum_le_sum (s:=core n L) hp
  simp only [sum_const,nsmul_eq_mul] at hs
  have hU : (0 : ℤ)≤(edges n L\usedEdges (fun a => ofPredicate n L (tri a) hL (ht a))).card := by positivity
  dsimp only at hd ⊢
  rw [perfect] at hd
  exact_mod_cast (by linarith : ((core n L).card : ℤ)≤(twoCoreEdges n L (fun a => ofPredicate n L (tri a) hL (ht a))).card)

omit hn hi in
/-- Empty actual multiple-point core is equivalent to the library's
pairwise determinant definition of simplicity. -/
theorem core_empty_iff_simple (hp : NoParallel n L) : core n L=∅ ↔ NoConcurrent n L := by
  classical
  constructor
  · intro hc i j k hij hjk hzero
    let p := intersection (L i) (L j)
    have hne : i≠j := ne_of_lt hij
    have hd := noParallel_any n L hp i j i.isLt j.isLt (fun h => hne (Fin.ext h))
    have hv : p∈vertices n L := mem_image.mpr ⟨(i,j),mem_offDiag.mpr ⟨mem_univ _,mem_univ _,hne⟩,rfl⟩
    have ho : OrdinaryAt n L p := by
      by_contra hno
      have hp : p∈core n L := mem_filter.mpr ⟨hv,hno⟩
      rw [hc] at hp
      exact notMem_empty p hp
    have hiP : affineEval (L i) p=0 := intersection_on_left _ _ hd
    have hjP : affineEval (L j) p=0 := intersection_on_right _ _ hd
    have hkP : affineEval (L k) p=0 := by
      dsimp [p]
      rw [eval_intersection _ _ _ hd,hzero]
      simp
    have he : j=k := ordinary_nonradial_unique n L p ho i j k hiP hjP hkP hne.symm (ne_of_lt (lt_trans hij hjk)).symm
    exact (ne_of_lt hjk) he
  · exact UpperSimpleOptimality.core_empty n L hp

/-- With no shared core-to-core side, a certificate attaining the exact
Tamura polynomial must come from a simple arrangement. The assumption is
weaker than requiring that no line contain two multiple points. -/
theorem perfect_no_core_sides_simple
    (empty : twoCoreEdges n L (fun a => ofPredicate n L (tri a) hL (ht a))=∅)
    (perfect : (n : ℤ)*(n-2)=3*Fintype.card α) : NoConcurrent n L := by
  have degree (p : Point) (_ : p∈core n L) :
      twoDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) p≤2 := by simp [twoDegree,empty]
  have hh := perfect_requires_core_cycle_count n L hL hn tri hi ht degree perfect
  simp only [empty,card_empty] at hh
  have hc : core n L=∅ := card_eq_zero.mp (by omega)
  exact (core_empty_iff_simple n L hL).mp hc

end Certificate
#print axioms certificate_local_degree_two
#print axioms certificate_degree_two_fan_sum
#print axioms certificate_degree_two_square_defect
#print axioms certificate_no_core_sides
#print axioms perfect_requires_core_cycle_count
#print axioms core_empty_iff_simple
#print axioms perfect_no_core_sides_simple
end Kobon.UpperOpenMathDegreeBudgets
