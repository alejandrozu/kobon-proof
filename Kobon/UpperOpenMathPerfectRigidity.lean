import Kobon.UpperOpenMathDegreeBudgets

/-! Equality rigidity for actual certificates at the Tamura polynomial.
Under maximum shared-core degree two, every possible multiple point must
be a triple fan with exactly two ordinary and two core shared sides. The
geometric exclusion of the remaining cycles is a separate problem. -/
namespace Kobon.UpperOpenMathPerfectRigidity
open Cells FanGeometry UpperVertexBudget UpperTriangleIncidence
  UpperSharedIncidence UpperEdgeInventory UpperCoreExtraction
  UpperOpenMathGlobalFans UpperOpenMathDegreeBudgets Finset
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem certificate_perfect_resources {α : Type*} [Fintype α]
    (n : Nat) (L : Nat→Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α→Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (degree : ∀ p∈core n L,
      twoDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) p≤2)
    (perfect : (n : ℤ)*(n-2)=3*Fintype.card α) :
    let G := fun a => ofPredicate n L (tri a) hL (ht a)
    (edges n L\usedEdges G).card=0 ∧
      (twoCoreEdges n L G).card=(core n L).card ∧
      (∑ p∈core n L, (((supports n L p).card : ℤ)-2)^2)=((core n L).card : ℤ) := by
  classical
  let G := fun a => ofPredicate n L (tri a) hL (ht a)
  have hd := certificate_degree_two_square_defect n L hL hn tri hi ht degree
  have htwo := two_degree_sum n L hL hn tri hi ht
  have hb (p : Point) (hp : p∈core n L) : (twoDegree n L G p : ℤ)≤2 := by
    exact_mod_cast degree p hp
  have hsum := sum_le_sum (s:=core n L) hb
  simp only [sum_const,nsmul_eq_mul] at hsum
  dsimp only at htwo hd
  rw [htwo] at hsum
  have hD : ((twoCoreEdges n L G).card : ℤ)≤(core n L).card := by linarith
  have hs (p : Point) (hp : p∈core n L) : (1 : ℤ)≤(((supports n L p).card : ℤ)-2)^2 := by
    have hr : (3 : ℤ)≤(supports n L p).card := by exact_mod_cast core_multiplicity n L hL hp
    nlinarith [sq_nonneg (((supports n L p).card : ℤ)-3)]
  have hsq := sum_le_sum (s:=core n L) hs
  simp only [sum_const,nsmul_eq_mul] at hsq
  have hU : (0 : ℤ)≤(edges n L\usedEdges G).card := by positivity
  rw [perfect] at hd
  have hu : ((edges n L\usedEdges G).card : ℤ)=0 := by linarith
  have he : ((twoCoreEdges n L G).card : ℤ)=(core n L).card := by linarith
  have hq : (∑ p∈core n L, (((supports n L p).card : ℤ)-2)^2)=((core n L).card : ℤ) := by linarith
  dsimp only
  exact ⟨by exact_mod_cast hu,by exact_mod_cast he,hq⟩

theorem certificate_balanced_resources {α : Type*} [Fintype α]
    (n : Nat) (L : Nat→Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α→Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (degree : ∀ p∈core n L,
      twoDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) p≤2)
    (balanced : (n : ℤ)*(n-2)=3*Fintype.card α+
      (edges n L\usedEdges (fun a => ofPredicate n L (tri a) hL (ht a))).card) :
    let G := fun a => ofPredicate n L (tri a) hL (ht a)
    (twoCoreEdges n L G).card=(core n L).card ∧
      (∑ p∈core n L, (((supports n L p).card : ℤ)-2)^2)=((core n L).card : ℤ) := by
  classical
  let G := fun a => ofPredicate n L (tri a) hL (ht a)
  have hd := certificate_degree_two_square_defect n L hL hn tri hi ht degree
  have htwo := two_degree_sum n L hL hn tri hi ht
  have hb (p : Point) (hp : p∈core n L) : (twoDegree n L G p : ℤ)≤2 := by
    exact_mod_cast degree p hp
  have hsum := sum_le_sum (s:=core n L) hb
  simp only [sum_const,nsmul_eq_mul] at hsum
  dsimp only at htwo hd
  rw [htwo] at hsum
  have hD : ((twoCoreEdges n L G).card : ℤ)≤(core n L).card := by linarith
  have hs (p : Point) (hp : p∈core n L) : (1 : ℤ)≤(((supports n L p).card : ℤ)-2)^2 := by
    have hr : (3 : ℤ)≤(supports n L p).card := by exact_mod_cast core_multiplicity n L hL hp
    nlinarith [sq_nonneg (((supports n L p).card : ℤ)-3)]
  have hsq := sum_le_sum (s:=core n L) hs
  simp only [sum_const,nsmul_eq_mul] at hsq
  rw [balanced] at hd
  have he : ((twoCoreEdges n L G).card : ℤ)=(core n L).card := by linarith
  have hq : (∑ p∈core n L, (((supports n L p).card : ℤ)-2)^2)=((core n L).card : ℤ) := by linarith
  dsimp only
  exact ⟨by exact_mod_cast he,hq⟩

/-- Equality between the polynomial deficit and the unused-edge count
has the same local rigidity even when that common count is positive. -/
theorem certificate_balanced_local_rigidity {α : Type*} [Fintype α]
    (n : Nat) (L : Nat→Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α→Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (degree : ∀ p∈core n L,
      twoDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) p≤2)
    (balanced : (n : ℤ)*(n-2)=3*Fintype.card α+
      (edges n L\usedEdges (fun a => ofPredicate n L (tri a) hL (ht a))).card) :
    let G := fun a => ofPredicate n L (tri a) hL (ht a)
    ∀ p∈core n L, (supports n L p).card=3 ∧
      oneDegree n L G p=2 ∧ twoDegree n L G p=2 := by
  classical
  let G := fun a => ofPredicate n L (tri a) hL (ht a)
  obtain ⟨hD2,hSq⟩ := certificate_balanced_resources n L hL hn tri hi ht degree balanced
  try dsimp only at hD2 hSq
  have hsqLower (p : Point) (hp : p∈core n L) : (1 : ℤ)≤(((supports n L p).card : ℤ)-2)^2 := by
    have hr : (3 : ℤ)≤(supports n L p).card := by exact_mod_cast core_multiplicity n L hL hp
    nlinarith [sq_nonneg (((supports n L p).card : ℤ)-3)]
  have hsqEqual : (∑ _p∈core n L, (1 : ℤ))=
      ∑ p∈core n L, (((supports n L p).card : ℤ)-2)^2 := by
    simpa only [sum_const,nsmul_eq_mul,mul_one] using hSq.symm
  have hsqEach := (sum_eq_sum_iff_of_le hsqLower).mp hsqEqual
  have htriple (p : Point) (hp : p∈core n L) : (supports n L p).card=3 := by
    have hr : (3 : ℤ)≤(supports n L p).card := by exact_mod_cast core_multiplicity n L hL hp
    have he := hsqEach p hp
    have hh : ((supports n L p).card : ℤ)=3 := by nlinarith
    exact_mod_cast hh
  have hsum2 := two_degree_sum n L hL hn tri hi ht
  dsimp only at hsum2
  rw [hD2] at hsum2
  have h2Each : ∀ p∈core n L, twoDegree n L G p=2 := by
    have he : (∑ p∈core n L, (twoDegree n L G p : ℤ))=
        ∑ _p∈core n L, (2 : ℤ) := by simpa only [sum_const,nsmul_eq_mul,mul_comm] using hsum2
    have hl (p : Point) (hp : p∈core n L) : (twoDegree n L G p : ℤ)≤2 := by
      exact_mod_cast degree p hp
    have h := (sum_eq_sum_iff_of_le hl).mp he
    intro p hp
    exact_mod_cast h p hp
  have hS : (∑ p∈core n L, (supports n L p).card*((supports n L p).card-2 : ℤ))=
      3*(core n L).card := by
    calc
      _=∑ _p∈core n L, (3 : ℤ) := sum_congr rfl (by intro p hp; rw [htriple p hp]; norm_num)
      _=_ := by simp [mul_comm]
  have hid := defect_identity n L hL hn tri hi ht
  dsimp only at hid
  rw [balanced,hD2,hS] at hid
  try simp only [Nat.cast_zero,sub_self] at hid
  have hD1 : ((oneCoreEdges n L G).card : ℤ)=2*(core n L).card := by
    dsimp [G]
    linarith only [hid]
  have hsum1 := one_degree_sum n L hL hn tri hi ht
  dsimp only at hsum1
  rw [hD1] at hsum1
  have h1Each : ∀ p∈core n L, oneDegree n L G p=2 := by
    have hl (p : Point) (hp : p∈core n L) : (oneDegree n L G p : ℤ)≤2 := by
      have hh := certificate_local_degree_two n L hL hn tri hi ht p hp (degree p hp)
      rw [htriple p hp] at hh
      exact_mod_cast hh
    have he : (∑ p∈core n L, (oneDegree n L G p : ℤ))=
        ∑ _p∈core n L, (2 : ℤ) := by simpa only [sum_const,nsmul_eq_mul,mul_comm] using hsum1
    have h := (sum_eq_sum_iff_of_le hl).mp he
    intro p hp
    exact_mod_cast h p hp
  exact fun p hp => ⟨htriple p hp,h1Each p hp,h2Each p hp⟩

theorem certificate_perfect_local_rigidity {α : Type*} [Fintype α]
    (n : Nat) (L : Nat→Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α→Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (degree : ∀ p∈core n L,
      twoDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) p≤2)
    (perfect : (n : ℤ)*(n-2)=3*Fintype.card α) :
    let G := fun a => ofPredicate n L (tri a) hL (ht a)
    ∀ p∈core n L, (supports n L p).card=3 ∧
      oneDegree n L G p=2 ∧ twoDegree n L G p=2 := by
  obtain ⟨hU,_,_⟩ := certificate_perfect_resources n L hL hn tri hi ht degree perfect
  apply certificate_balanced_local_rigidity n L hL hn tri hi ht degree
  rw [hU]
  simpa using perfect

#print axioms certificate_perfect_resources
#print axioms certificate_balanced_resources
#print axioms certificate_balanced_local_rigidity
#print axioms certificate_perfect_local_rigidity
end Kobon.UpperOpenMathPerfectRigidity
