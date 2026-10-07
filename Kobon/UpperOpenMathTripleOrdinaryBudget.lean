import Kobon.UpperOpenMathMarkedPoverty
import Kobon.UpperOpenMathCoreDoubleCount

/-!
# A general ordinary-to-core bound for triple-only arrangements

The total shared-edge bound `D <= 2q` is false. The ordinary-to-core count
satisfies the stronger valid statement `D1 + 2*e <= 2q`, where e counts the
extremal ordinary-degree-three cores. The proof pays each such core's three
marked edges at distinct low targets of core degree at most two. This is an
actual all-order geometric theorem, with no planar graph assumption.
-/
namespace Kobon.UpperOpenMathTripleOrdinaryBudget
open Cells FanGeometry UpperVertexBudget UpperTriangleIncidence UpperSharedIncidence
  UpperCoreExtraction UpperOpenMathCapHeavyTriples Finset
open scoped BigOperators

theorem certificate_ordinary_budget_with_extremals {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (triples : ∀ c∈core n L, (supports n L c).card=3) :
    let G := fun a => ofPredicate n L (tri a) hL (ht a)
    (oneCoreEdges n L G).card+
      2*((core n L).filter (fun c => ordinaryDegree n L G c=3)).card≤2*(core n L).card := by
  classical
  let G := fun a => ofPredicate n L (tri a) hL (ht a)
  let C := core n L
  let E := C.filter (fun c => ordinaryDegree n L G c=3)
  let B := C.filter (fun c => ordinaryDegree n L G c≤1 ∧
    ordinaryDegree n L G c+coreDegree n L G c≤2)
  have hESub : E⊆C := filter_subset _ _
  have hBSub : B⊆C := filter_subset _ _
  have hInd (e : Edge) (he : e∈twoCoreEdges n L G) : (e∩E).card≤1 := by
    apply card_le_one.mpr
    intro p hp q hq
    by_contra hpq
    obtain ⟨hpe,hpE⟩ := mem_inter.mp hp
    obtain ⟨hqe,hqE⟩ := mem_inter.mp hq
    have hpC := (mem_filter.mp hpE).1
    have hqC := (mem_filter.mp hqE).1
    have hpair : e={p,q} := by
      apply Eq.symm
      apply eq_of_subset_of_card_le
      · intro x hx
        simp only [mem_insert,mem_singleton] at hx
        rcases hx with rfl|rfl <;> assumption
      · rw [card_pair hpq,used_edge_card G (mem_filter.mp (mem_sdiff.mp he).1).1]
    exact certificate_cap_heavy_not_adjacent n L hL hn tri hi ht p q hpC hqC
      ⟨triples p hpC,Or.inl (mem_filter.mp hpE).2⟩
      ⟨triples q hqC,Or.inl (mem_filter.mp hqE).2⟩ (by simpa only [hpair] using he)
  have hEdge (e : Edge) (he : e∈twoCoreEdges n L G) : (e∩E).card≤(e∩B).card := by
    by_cases hEmpty : e∩E=∅
    · simp [hEmpty]
    · obtain ⟨p,hp⟩ := nonempty_iff_ne_empty.mpr hEmpty
      obtain ⟨hpEdge,hpE⟩ := mem_inter.mp hp
      have hpC := (mem_filter.mp hpE).1
      have hused := (mem_filter.mp (mem_sdiff.mp he).1).1
      obtain ⟨q,hqp,heq⟩ := UpperOpenMathActualFans.pair_of_card_two_of_mem e p hpEdge (used_edge_card G hused)
      have hqEdge : q∈e := by simp [heq]
      have hqC : q∈C := mem_filter.mpr
        ⟨UpperEdgeInventory.certificate_side_vertices n L hL tri ht hused hqEdge,
          twoCore_endpoints n L G he q hqEdge⟩
      have poor := UpperOpenMathMarkedPoverty.certificate_extremal_neighbor_sum n L hL hn tri hi ht
        p q hpC hqC (triples p hpC) (triples q hqC) (mem_filter.mp hpE).2
        (by simpa only [heq] using he)
      have hB : q∈B := mem_filter.mpr ⟨hqC,poor⟩
      have hpos : 1≤(e∩B).card := card_pos.mpr ⟨q,mem_inter.mpr ⟨hqEdge,hB⟩⟩
      exact (hInd e he).trans hpos
  have hCount : (∑ p∈E, coreDegree n L G p)≤∑ p∈B, coreDegree n L G p := by
    change (∑ p∈E, ((twoCoreEdges n L G).filter (fun e => p∈e)).card)≤
      ∑ p∈B, ((twoCoreEdges n L G).filter (fun e => p∈e)).card
    rw [UpperOpenMathCoreDoubleCount.endpoint_double_count,
      UpperOpenMathCoreDoubleCount.endpoint_double_count]
    exact sum_le_sum hEdge
  have hE : (∑ p∈E, coreDegree n L G p)=3*E.card := by
    calc
      _=∑ _p∈E, 3 := by
        apply sum_congr rfl
        intro p hp
        obtain ⟨hpC,hpOrd⟩ := mem_filter.mp hp
        have hext : 2*(supports n L p).card-3≤
            ((oneCoreEdges n L G).filter (fun e => p∈e)).card := by
          rw [triples p hpC]
          change 3≤ordinaryDegree n L G p
          exact Nat.le_of_eq hpOrd.symm
        exact UpperOpenMathSupportedCores.certificate_extremal_neighbor_count
          n L hL hn tri hi ht p hpC hext
      _=3*E.card := by simp [Nat.mul_comm]
  have hB : (∑ p∈B, coreDegree n L G p)≤2*B.card := by
    calc
      _≤∑ _p∈B, 2 := sum_le_sum (fun p hp => by
        have h := (mem_filter.mp hp).2.2
        omega)
      _=2*B.card := by simp [Nat.mul_comm]
  have hThree : 3*E.card≤2*B.card := by rw [← hE]; exact hCount.trans hB
  have hPoint (p : Point) (hp : p∈C) :
      (ordinaryDegree n L G p : ℤ)≤2+(if p∈E then 1 else 0)-
        (if p∈B then coreDegree n L G p else 0) := by
    have hcap := UpperOpenMathActualFans.certificate_local_fan_bound n L hL hn tri hi ht p hp
    rw [triples p hp] at hcap
    change ordinaryDegree n L G p≤3 at hcap
    by_cases he : p∈E
    · have ho := (mem_filter.mp he).2
      have hb : p∉B := by intro hb; have hh := (mem_filter.mp hb).2.1; omega
      simp only [he,hb,ite_true,ite_false]
      omega
    · have ho : ordinaryDegree n L G p≠3 := fun h => he (mem_filter.mpr ⟨hp,h⟩)
      by_cases hb : p∈B
      · have hl := (mem_filter.mp hb).2.2
        simp only [he,hb,ite_true,ite_false]
        omega
      · simp only [he,hb,ite_true,ite_false]
        omega
  have hSum := sum_le_sum hPoint
  have hEfilter : C.filter (fun p => p∈E)=E := by
    rw [filter_mem_eq_inter,inter_eq_right.mpr hESub]
  have hBfilter : C.filter (fun p => p∈B)=B := by
    rw [filter_mem_eq_inter,inter_eq_right.mpr hBSub]
  have hEcount : (∑ p∈C, if p∈E then (1 : ℤ) else 0)=E.card := by
    simp [inter_eq_right.mpr hESub]
  have hBcount : (∑ p∈C, if p∈B then (coreDegree n L G p : ℤ) else 0)=
      ∑ p∈B, (coreDegree n L G p : ℤ) := by
    rw [← sum_filter,hBfilter]
  have hD := UpperOpenMathCoreDoubleCount.one_core_incidence_sum n L hL tri hi ht
  change (∑ p∈C, ordinaryDegree n L G p)=(oneCoreEdges n L G).card at hD
  have hDZ : (∑ p∈C, (ordinaryDegree n L G p : ℤ))=((oneCoreEdges n L G).card : ℤ) := by exact_mod_cast hD
  simp only [sum_sub_distrib,sum_add_distrib,sum_const,nsmul_eq_mul] at hSum
  simp only [Nat.cast_ite,Nat.cast_zero] at hSum
  rw [hDZ,hEcount,hBcount] at hSum
  have hECountZ : (∑ p∈E, (coreDegree n L G p : ℤ))=3*(E.card : ℤ) := by exact_mod_cast hE
  have hCountZ : (∑ p∈E, (coreDegree n L G p : ℤ))≤
      ∑ p∈B, (coreDegree n L G p : ℤ) := by exact_mod_cast hCount
  have hFinal : ((oneCoreEdges n L G).card : ℤ)+2*E.card≤2*C.card := by omega
  exact_mod_cast hFinal

theorem certificate_ordinary_to_core_bound {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (triples : ∀ c∈core n L, (supports n L c).card=3) :
    let G := fun a => ofPredicate n L (tri a) hL (ht a)
    (oneCoreEdges n L G).card≤2*(core n L).card := by
  have h := certificate_ordinary_budget_with_extremals n L hL hn tri hi ht triples
  dsimp only at h
  omega

/-- Triple-only near-optimal arrangements need a sufficiently dense actual
shared-core graph. A forest therefore cannot attain zero Tamura defect. -/
theorem certificate_triple_defect_core_density_with_extremals {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (triples : ∀ c∈core n L, (supports n L c).card=3) :
    let G := fun a => ofPredicate n L (tri a) hL (ht a)
    ((core n L).card : ℤ)+
      2*((core n L).filter (fun c => ordinaryDegree n L G c=3)).card+
      (UpperEdgeInventory.edges n L\usedEdges G).card-(twoCoreEdges n L G).card≤
      (n : ℤ)*(n-2)-3*Fintype.card α := by
  classical
  let G := fun a => ofPredicate n L (tri a) hL (ht a)
  have hD := certificate_ordinary_budget_with_extremals n L hL hn tri hi ht triples
  have hDZ : ((oneCoreEdges n L G).card : ℤ)+
      2*((core n L).filter (fun c => ordinaryDegree n L G c=3)).card≤
      2*(core n L).card := by exact_mod_cast hD
  have hS : (∑ p∈core n L, (supports n L p).card*((supports n L p).card-2 : ℤ))=
      3*(core n L).card := by
    calc
      _=∑ _p∈core n L, (3 : ℤ) := by
        apply sum_congr rfl
        intro p hp
        rw [triples p hp]
        norm_num
      _=3*(core n L).card := by simp [mul_comm]
  have hid := UpperCoreExtraction.defect_identity n L hL hn tri hi ht
  rw [hS] at hid
  dsimp only at hid
  linarith

theorem certificate_triple_defect_core_density {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (triples : ∀ c∈core n L, (supports n L c).card=3) :
    let G := fun a => ofPredicate n L (tri a) hL (ht a)
    ((core n L).card : ℤ)+(UpperEdgeInventory.edges n L\usedEdges G).card-(twoCoreEdges n L G).card≤
      (n : ℤ)*(n-2)-3*Fintype.card α := by
  have h := certificate_triple_defect_core_density_with_extremals n L hL hn tri hi ht triples
  dsimp only at h
  have hcard : 0≤ (((core n L).filter (fun c => ordinaryDegree n L
      (fun a => ofPredicate n L (tri a) hL (ht a)) c=3)).card : ℤ) := by positivity
  omega

#print axioms certificate_ordinary_budget_with_extremals
#print axioms certificate_ordinary_to_core_bound
#print axioms certificate_triple_defect_core_density_with_extremals
#print axioms certificate_triple_defect_core_density
end Kobon.UpperOpenMathTripleOrdinaryBudget
