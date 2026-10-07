import Kobon.UpperOpenMathBoundaryBudgets

/-! Sharp rounding for even orders and arrangements with few multiple
points. These are actual geometric bounds; no claim is made that every
arrangement has few cores. -/
namespace Kobon.UpperOpenMathSparseUpper
open Cells FanGeometry UpperVertexBudget UpperTriangleIncidence
  UpperSharedIncidence UpperCoreExtraction UpperCoreCombinatorics UpperOpenMathGlobalFans
  UpperOpenMathBoundaryBudgets Finset
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem even_polynomial_mod_three (m : ℤ) : (2*m*(4*m-5))%3≠2 := by
  have h0 := Int.emod_nonneg m (by norm_num : (3 : ℤ)≠0)
  have h3 := Int.emod_lt_of_pos m (by norm_num : (0 : ℤ)<3)
  have hc : m%3=0 ∨ m%3=1 ∨ m%3=2 := by omega
  rcases hc with hc|hc|hc <;> norm_num [Int.mul_emod,Int.sub_emod,hc]

/-- An additive four-unit polynomial slack gives the same rounded count
as two units at every even order. -/
theorem even_rounding (n T : Nat) (heven : n%2=0)
    (h : 6*(T : ℤ)≤(n : ℤ)*(2*n-5)+4) :
    6*(T : ℤ)≤(n : ℤ)*(2*n-5)+2 := by
  let m : ℤ := n/2
  have hn : (n : ℤ)=2*m := by dsimp [m]; omega
  have hform : (n : ℤ)*(2*n-5)=2*m*(4*m-5) := by rw [hn]; ring
  have hmod3 : ((n : ℤ)*(2*n-5))%3≠2 := by rw [hform]; exact even_polynomial_mod_three m
  have hmod2 : ((n : ℤ)*(2*n-5))%2=0 := by
    rw [hform,show 2*m*(4*m-5)=2*(m*(4*m-5)) by ring]
    omega
  omega

theorem certificate_one_core_upper {α : Type*} [Fintype α]
    (n : Nat) (L : Nat→Line ℝ) (hL : NoParallel n L) (hn : 4≤n)
    (heven : n%2=0) (tri : α→Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (small : (core n L).card≤1) :
    6*(Fintype.card α : ℤ)≤(n : ℤ)*(2*n-5)+2 := by
  have hd := certificate_three_core_defect n L hL hn heven tri hi ht (by omega)
  have he := core_edge_count n L hL tri ht
  have hc := Nat.choose_le_choose 2 small
  norm_num at hc
  have hD : (twoCoreEdges n L (fun a => ofPredicate n L (tri a) hL (ht a))).card=0 := by omega
  dsimp only at hd
  rw [hD] at hd
  simp only [Nat.cast_zero,sub_zero] at hd
  have hq : ((core n L).card : ℤ)≤1 := by exact_mod_cast small
  have hne : (n : ℤ)=2*(n/2 : Nat) := by omega
  have hb : (n : ℤ)-3≤2*((n : ℤ)*(n-2)-3*Fintype.card α) := by linarith
  have hb2 : (n : ℤ)-2≤2*((n : ℤ)*(n-2)-3*Fintype.card α) := by omega
  nlinarith

theorem multiplicity_remainder_bound (n : Nat) (L : Nat→Line ℝ)
    (hL : NoParallel n L) :
    (-3 : ℤ)*((core n L).filter (fun p => (supports n L p).card=3)).card≤
      ∑ p∈core n L,
        (2*((supports n L p).card : ℤ)^2-11*(supports n L p).card+12) := by
  classical
  have hp (p : Point) (hc : p∈core n L) :
      (if (supports n L p).card=3 then -3 else 0 : ℤ)≤
        2*((supports n L p).card : ℤ)^2-11*(supports n L p).card+12 := by
    have hr : (3 : ℤ)≤(supports n L p).card := by exact_mod_cast core_multiplicity n L hL hc
    split_ifs with he
    · rw [he]
      norm_num
    · have hr4 : (4 : ℤ)≤(supports n L p).card := by omega
      have hpos := mul_nonneg (sub_nonneg.mpr hr4)
        (by omega : (0 : ℤ)≤2*(supports n L p).card-3)
      nlinarith
  have hs := sum_le_sum (s:=core n L) hp
  simpa only [Finset.sum_ite,Finset.sum_const_zero,add_zero,
    sum_const,nsmul_eq_mul,mul_comm] using hs

theorem certificate_two_core_at_most_one_triple_upper {α : Type*} [Fintype α]
    (n : Nat) (L : Nat→Line ℝ) (hL : NoParallel n L) (hn : 4≤n)
    (heven : n%2=0) (tri : α→Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (small : (core n L).card≤2)
    (fewTriples : ((core n L).filter (fun p => (supports n L p).card=3)).card≤1) :
    6*(Fintype.card α : ℤ)≤(n : ℤ)*(2*n-5)+2 := by
  classical
  have hd := certificate_boundary_defect_even n L hL hn heven tri hi ht
  have hb := UpperOpenMathCoreHull.boundary_card (core n L)
  rw [Nat.min_eq_left (by omega : (core n L).card≤3)] at hb
  have hbZ : ((core n L).card : ℤ)≤(UpperOpenMathCoreHull.boundary (core n L)).card := by exact_mod_cast hb
  have he := core_edge_count n L hL tri ht
  have hc := Nat.choose_le_choose 2 small
  norm_num at hc
  have hD : ((twoCoreEdges n L (fun a => ofPredicate n L (tri a) hL (ht a))).card : ℤ)≤1 := by
    have hh : (twoCoreEdges n L (fun a => ofPredicate n L (tri a) hL (ht a))).card≤1 := by omega
    exact_mod_cast hh
  have hm := multiplicity_remainder_bound n L hL
  have htrip : (((core n L).filter (fun p => (supports n L p).card=3)).card : ℤ)≤1 := by exact_mod_cast fewTriples
  have hweight : (∑ p∈core n L,
      (2*((supports n L p).card : ℤ)^2-11*(supports n L p).card+12))=
      2*(∑ p∈core n L, (supports n L p).card*((supports n L p).card-2 : ℤ))-
      7*(∑ p∈core n L, ((supports n L p).card : ℤ))+12*(core n L).card := by
    calc
      _=∑ p∈core n L,
          (2*((supports n L p).card*((supports n L p).card-2 : ℤ))-
            7*(supports n L p).card+12) := sum_congr rfl (by intro p hp; ring)
      _=_ := by simp [sum_add_distrib,sum_sub_distrib,← mul_sum,sum_const,nsmul_eq_mul,mul_comm]
  rw [hweight] at hm
  dsimp only at hd
  have hb4 : 6*(Fintype.card α : ℤ)≤(n : ℤ)*(2*n-5)+4 := by nlinarith
  exact even_rounding n _ heven hb4

#print axioms certificate_one_core_upper
#print axioms certificate_two_core_at_most_one_triple_upper
end Kobon.UpperOpenMathSparseUpper
