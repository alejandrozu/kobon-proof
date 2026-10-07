import Kobon.UpperOpenMathMarkedPoverty
import Kobon.UpperOpenMathCoreDoubleCount

/-!
# Ordinary-cap discharging with arbitrary multiple-point orders

Extremal triple fans are paid at their actual neighboring vertices. A
neighboring triple has low total sharing degree; a higher-order core pays
from its quadratic multiplicity surplus. No independence assumption is made
for higher-order fans. This yields an all-order mixed-multiplicity defect
bound, including a quantitative saving at the poor triple targets.
-/
namespace Kobon.UpperOpenMathMixedCapBudget
open Cells FanGeometry UpperVertexBudget UpperTriangleIncidence UpperSharedIncidence
  UpperCoreExtraction UpperOpenMathCapHeavyTriples UpperOpenMathRadialOrder
  UpperOpenMathActualFans Finset
open scoped BigOperators

noncomputable def higherCores (n : ℕ) (L : ℕ → Line ℝ) : Finset Point := by
  classical
  exact (core n L).filter (fun p => 4≤(supports n L p).card)

noncomputable def poorTripleCores {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (G : α → TriangleGeometry) : Finset Point := by
  classical
  exact (core n L).filter (fun p => (supports n L p).card=3 ∧
    ordinaryDegree n L G p≤1 ∧ ordinaryDegree n L G p+coreDegree n L G p≤2)

noncomputable def higherWeight (n : ℕ) (L : ℕ → Line ℝ) : ℤ :=
  ∑ p∈higherCores n L, ((supports n L p).card*((supports n L p).card-4 : ℤ)+1)

theorem certificate_local_combined_degree {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a)) (p : Point) (hp : p∈core n L) :
    let G := fun a => ofPredicate n L (tri a) hL (ht a)
    ordinaryDegree n L G p+coreDegree n L G p≤2*(supports n L p).card := by
  classical
  have hr := core_multiplicity n L hL hp
  letI : NeZero (2*(supports n L p).card) := ⟨by omega⟩
  let D := atPoint n L hL hn p
  let f := fan n L hL hn tri ht p (mem_filter.mp hp).1 D (by omega)
  have hs := card_le_card (subset_univ f.shared)
  simp only [card_univ,ZMod.card] at hs
  have hsplit := f.shared_card_split
  rw [fan_ordinary_card n L hL hn tri ht p (mem_filter.mp hp).1 D (by omega) hi hp,
    fan_core_card n L hL hn tri ht p (mem_filter.mp hp).1 D (by omega) hi hp] at hsplit
  change ordinaryDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) p+
    coreDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) p=f.shared.card at hsplit
  rw [← hsplit] at hs
  exact hs

theorem certificate_mixed_weighted_budget {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a)) :
    let G := fun a => ofPredicate n L (tri a) hL (ht a)
    3*((oneCoreEdges n L G).card : ℤ)+3*(core n L).card+3*higherWeight n L+
      2*(∑ p∈poorTripleCores n L G, (coreDegree n L G p : ℤ))≤
      3*(∑ p∈core n L, (supports n L p).card*((supports n L p).card-2 : ℤ)) := by
  classical
  let G := fun a => ofPredicate n L (tri a) hL (ht a)
  let C := core n L
  let E := C.filter (fun p => (supports n L p).card=3 ∧ ordinaryDegree n L G p=3)
  let H := higherCores n L
  let B := poorTripleCores n L G
  let K := B∪H
  let w := fun p => (supports n L p).card*((supports n L p).card-2 : ℤ)-1-ordinaryDegree n L G p
  let A := fun p => (supports n L p).card*((supports n L p).card-4 : ℤ)+1
  have eSub : E⊆C := filter_subset _ _
  have hSub : H⊆C := filter_subset _ _
  have bSub : B⊆C := filter_subset _ _
  have kSub : K⊆C := union_subset bSub hSub
  have hE (p : Point) (hp : p∈E) : coreDegree n L G p=3 := by
    obtain ⟨hpC,hpR,hpA⟩ := mem_filter.mp hp
    have hext : 2*(supports n L p).card-3≤ordinaryDegree n L G p := by rw [hpR,hpA]
    exact UpperOpenMathSupportedCores.certificate_extremal_neighbor_count n L hL hn tri hi ht p hpC hext
  have hInd (e : Edge) (he : e∈twoCoreEdges n L G) : (e∩E).card≤1 := by
    apply card_le_one.mpr
    intro p hp q hq
    by_contra hpq
    obtain ⟨hpe,hpE⟩ := mem_inter.mp hp
    obtain ⟨hqe,hqE⟩ := mem_inter.mp hq
    have hpair : e={p,q} := by
      apply Eq.symm
      apply eq_of_subset_of_card_le
      · intro x hx
        rcases mem_insert.mp hx with hx|hx
        · simpa only [hx] using hpe
        · simpa only [mem_singleton.mp hx] using hqe
      · rw [card_pair hpq,used_edge_card G (mem_filter.mp (mem_sdiff.mp he).1).1]
    have hpC := (mem_filter.mp hpE).1
    have hqC := (mem_filter.mp hqE).1
    exact certificate_cap_heavy_not_adjacent n L hL hn tri hi ht p q hpC hqC
      ⟨(mem_filter.mp hpE).2.1,Or.inl (mem_filter.mp hpE).2.2⟩
      ⟨(mem_filter.mp hqE).2.1,Or.inl (mem_filter.mp hqE).2.2⟩
      (by simpa only [hpair] using he)
  have hEdge (e : Edge) (he : e∈twoCoreEdges n L G) : (e∩E).card≤(e∩K).card := by
    by_cases hEmpty : e∩E=∅
    · simp [hEmpty]
    · obtain ⟨p,hp⟩ := nonempty_iff_ne_empty.mpr hEmpty
      obtain ⟨hpEdge,hpE⟩ := mem_inter.mp hp
      obtain ⟨hpC,hpR,hpA⟩ := mem_filter.mp hpE
      have hused := (mem_filter.mp (mem_sdiff.mp he).1).1
      obtain ⟨q,hqp,heq⟩ := pair_of_card_two_of_mem e p hpEdge (used_edge_card G hused)
      have hqEdge : q∈e := by simp [heq]
      have hqC : q∈C := mem_filter.mpr
        ⟨UpperEdgeInventory.certificate_side_vertices n L hL tri ht hused hqEdge,
          twoCore_endpoints n L G he q hqEdge⟩
      have hqR := core_multiplicity n L hL hqC
      have hqK : q∈K := by
        by_cases hr : (supports n L q).card=3
        · have poor := UpperOpenMathMarkedPoverty.certificate_extremal_neighbor_sum n L hL hn tri hi ht
            p q hpC hqC hpR hr hpA (by simpa only [heq] using he)
          exact mem_union.mpr (Or.inl (mem_filter.mpr ⟨hqC,hr,poor⟩))
        · exact mem_union.mpr (Or.inr (mem_filter.mpr ⟨hqC,by omega⟩))
      have hpos : 1≤(e∩K).card := card_pos.mpr ⟨q,mem_inter.mpr ⟨hqEdge,hqK⟩⟩
      exact (hInd e he).trans hpos
  have hCount : (∑ p∈E, coreDegree n L G p)≤∑ p∈K, coreDegree n L G p := by
    change (∑ p∈E, ((twoCoreEdges n L G).filter (fun e => p∈e)).card)≤
      ∑ p∈K, ((twoCoreEdges n L G).filter (fun e => p∈e)).card
    rw [UpperOpenMathCoreDoubleCount.endpoint_double_count,
      UpperOpenMathCoreDoubleCount.endpoint_double_count]
    exact sum_le_sum hEdge
  have hEsum : (∑ p∈E, coreDegree n L G p)=3*E.card := by
    calc
      _=∑ _p∈E, 3 := sum_congr rfl hE
      _=3*E.card := by simp [Nat.mul_comm]
  have hCountZ : (3 : ℤ)*E.card≤∑ p∈K, (coreDegree n L G p : ℤ) := by
    have hh := hCount
    rw [hEsum] at hh
    exact_mod_cast hh
  have hPoint (p : Point) (hp : p∈C) :
      (if p∈K then (coreDegree n L G p : ℤ) else 0)+
      (if p∈B then 2*(coreDegree n L G p : ℤ) else 0)+
      (if p∈H then 3*A p else 0)-(if p∈E then 3 else 0)≤3*w p := by
    have hr := core_multiplicity n L hL hp
    have hcap := certificate_local_fan_bound n L hL hn tri hi ht p hp
    have hcmb := certificate_local_combined_degree n L hL hn tri hi ht p hp
    change ordinaryDegree n L G p≤2*(supports n L p).card-3 at hcap
    change ordinaryDegree n L G p+coreDegree n L G p≤2*(supports n L p).card at hcmb
    by_cases he : p∈E
    · obtain ⟨hpC,hpR,hpA⟩ := mem_filter.mp he
      have hd := hE p he
      have hh : p∉H := by intro h; have := (mem_filter.mp h).2; omega
      have hb : p∉B := by intro h; have := (mem_filter.mp h).2.2.1; omega
      have hk : p∉K := by simpa only [K,mem_union,not_or] using ⟨hb,hh⟩
      simp only [he,hk,hb,hh,ite_true,ite_false,w,hpR,hpA]
      norm_num
    · by_cases hh : p∈H
      · have h4 := (mem_filter.mp hh).2
        have hb : p∉B := by intro h; have := (mem_filter.mp h).2.1; omega
        have hk : p∈K := mem_union.mpr (Or.inr hh)
        have hrZ : (4 : ℤ)≤(supports n L p).card := by exact_mod_cast h4
        have haZ : (ordinaryDegree n L G p : ℤ)+3≤2*(supports n L p).card := by
          have hhN : ordinaryDegree n L G p+3≤2*(supports n L p).card := by omega
          exact_mod_cast hhN
        have hcombZ : (ordinaryDegree n L G p : ℤ)+coreDegree n L G p≤2*(supports n L p).card := by
          exact_mod_cast hcmb
        simp only [he,hh,hb,hk,ite_true,ite_false,w,A]
        nlinarith
      · have rp : (supports n L p).card=3 := by
          have nh : ¬4≤(supports n L p).card := fun h => hh (mem_filter.mpr ⟨hp,h⟩)
          omega
        have na : ordinaryDegree n L G p≠3 := fun h => he (mem_filter.mpr ⟨hp,rp,h⟩)
        by_cases hb : p∈B
        · have low := (mem_filter.mp hb).2.2.2
          have hk : p∈K := mem_union.mpr (Or.inl hb)
          simp only [he,hh,hb,hk,ite_true,ite_false,w,rp]
          omega
        · have hk : p∉K := by simpa only [K,mem_union,not_or] using ⟨hb,hh⟩
          rw [rp] at hcap
          simp only [he,hh,hb,hk,ite_true,ite_false,w,rp]
          omega
  have hSum := sum_le_sum hPoint
  have filterK : C.filter (fun p => p∈K)=K := by rw [filter_mem_eq_inter,inter_eq_right.mpr kSub]
  have filterB : C.filter (fun p => p∈B)=B := by rw [filter_mem_eq_inter,inter_eq_right.mpr bSub]
  have filterH : C.filter (fun p => p∈H)=H := by rw [filter_mem_eq_inter,inter_eq_right.mpr hSub]
  have filterE : C.filter (fun p => p∈E)=E := by rw [filter_mem_eq_inter,inter_eq_right.mpr eSub]
  simp only [sum_sub_distrib,sum_add_distrib,← mul_sum] at hSum
  have ksum : (∑ p∈C, if p∈K then (coreDegree n L G p : ℤ) else 0)=
      ∑ p∈K, (coreDegree n L G p : ℤ) := by rw [← sum_filter,filterK]
  have bsum : (∑ p∈C, if p∈B then 2*(coreDegree n L G p : ℤ) else 0)=
      2*(∑ p∈B, (coreDegree n L G p : ℤ)) := by rw [← sum_filter,filterB,← mul_sum]
  have hsum : (∑ p∈C, if p∈H then 3*A p else 0)=3*higherWeight n L := by
    rw [← sum_filter,filterH,← mul_sum]
    rfl
  have esum : (∑ p∈C, if p∈E then (3 : ℤ) else 0)=3*E.card := by
    rw [← sum_filter,filterE]
    simp [mul_comm]
  rw [ksum,bsum,hsum,esum] at hSum
  have hW : 3*higherWeight n L+2*(∑ p∈B, (coreDegree n L G p : ℤ))≤3*(∑ p∈C, w p) := by
    linarith
  have hD := UpperOpenMathCoreDoubleCount.one_core_incidence_sum n L hL tri hi ht
  have hDZ : (∑ p∈C, (ordinaryDegree n L G p : ℤ))=(oneCoreEdges n L G).card := by exact_mod_cast hD
  have hwSum : (∑ p∈C, w p)=
      (∑ p∈C, (supports n L p).card*((supports n L p).card-2 : ℤ))-
      C.card-(oneCoreEdges n L G).card := by
    simp only [w,sum_sub_distrib,sum_const,nsmul_eq_mul,mul_one]
    rw [hDZ]
  rw [hwSum] at hW
  dsimp only
  change 3*((oneCoreEdges n L G).card : ℤ)+3*C.card+3*higherWeight n L+
    2*(∑ p∈B, (coreDegree n L G p : ℤ))≤
    3*(∑ p∈C, (supports n L p).card*((supports n L p).card-2 : ℤ))
  linarith

theorem higher_weight_ge_card (n : ℕ) (L : ℕ → Line ℝ) :
    ((higherCores n L).card : ℤ)≤higherWeight n L := by
  classical
  have each (p : Point) (hp : p∈higherCores n L) :
      (1 : ℤ)≤(supports n L p).card*((supports n L p).card-4 : ℤ)+1 := by
    have hr : (4 : ℤ)≤(supports n L p).card := by exact_mod_cast (mem_filter.mp hp).2
    nlinarith [mul_nonneg (by omega : (0 : ℤ)≤(supports n L p).card)
      (by omega : (0 : ℤ)≤(supports n L p).card-4)]
  have h := sum_le_sum each
  simpa only [sum_const,nsmul_eq_mul,mul_one,higherWeight] using h

theorem certificate_mixed_ordinary_budget {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a)) :
    let G := fun a => ofPredicate n L (tri a) hL (ht a)
    ((oneCoreEdges n L G).card : ℤ)+(core n L).card+higherWeight n L≤
      ∑ p∈core n L, (supports n L p).card*((supports n L p).card-2 : ℤ) := by
  classical
  let G := fun a => ofPredicate n L (tri a) hL (ht a)
  have h := certificate_mixed_weighted_budget n L hL hn tri hi ht
  have positive : 0≤∑ p∈poorTripleCores n L G, (coreDegree n L G p : ℤ) :=
    sum_nonneg (fun _ _ => by positivity)
  dsimp only at h
  change ((oneCoreEdges n L G).card : ℤ)+(core n L).card+higherWeight n L≤_
  linarith

theorem certificate_mixed_weighted_defect {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a)) :
    let G := fun a => ofPredicate n L (tri a) hL (ht a)
    3*(core n L).card+3*higherWeight n L+
      3*(UpperEdgeInventory.edges n L\usedEdges G).card-3*(twoCoreEdges n L G).card+
      2*(∑ p∈poorTripleCores n L G, (coreDegree n L G p : ℤ))≤
      3*((n : ℤ)*(n-2)-3*Fintype.card α) := by
  have h := certificate_mixed_weighted_budget n L hL hn tri hi ht
  have hid := defect_identity n L hL hn tri hi ht
  dsimp only at h hid ⊢
  linarith

theorem certificate_mixed_core_defect {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a)) :
    let G := fun a => ofPredicate n L (tri a) hL (ht a)
    (core n L).card+higherWeight n L+
      (UpperEdgeInventory.edges n L\usedEdges G).card-(twoCoreEdges n L G).card≤
      (n : ℤ)*(n-2)-3*Fintype.card α := by
  have h := certificate_mixed_ordinary_budget n L hL hn tri hi ht
  have hid := defect_identity n L hL hn tri hi ht
  dsimp only at h hid ⊢
  linarith

#print axioms certificate_mixed_weighted_budget
#print axioms certificate_mixed_core_defect
end Kobon.UpperOpenMathMixedCapBudget
