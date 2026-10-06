import Kobon.UpperOpenMathComponentPenalty

/-! Triple fans with at most three shared core sides. The missing five-ray
pattern supplies a curvature inequality, and actual extremal-to-poor
matching pays the only negative local fans. -/
namespace Kobon.UpperOpenMathTripleDegreeThree
open Cells FanGeometry UpperFan UpperVertexBudget UpperTriangleIncidence
  UpperSharedIncidence UpperCoreExtraction UpperOpenMathRadialOrder
  UpperOpenMathActualFans UpperOpenMathCapHeavyTriples UpperOpenMathCoreComponents Finset
open scoped BigOperators
set_option maxHeartbeats 1000000

set_option maxRecDepth 1000000 in
theorem finite_shared_not_five : ∀ T : Finset (ZMod 6),
    (UpperOpenMathPartialTriple.finite_shared T).card≠5 := by
  decide +kernel

theorem triple_shared_not_five {n : ℕ} {L : ℕ → Line ℝ}
    (f : UpperFan.Sectors n 3 L) : f.ordinaryShared.card+f.coreShared.card≠5 := by
  rw [f.shared_card_split]
  exact finite_shared_not_five f.triangular

theorem certificate_triple_not_five {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (p : Point) (hp : p∈core n L) (triple : (supports n L p).card=3) :
    ordinaryDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) p+
      coreDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) p≠5 := by
  classical
  letI : NeZero (2*(supports n L p).card) := ⟨by omega⟩
  let D := atPoint n L hL hn p
  let f := fan n L hL hn tri ht p (mem_filter.mp hp).1 D (by omega)
  have hfinite : f.ordinaryShared.card+f.coreShared.card≠5 := by
    have hf : ∀ T : Finset (ZMod (2*(supports n L p).card)),
        (T.filter (fun z => z-1∈T)).card≠5 := by
      rw [triple]
      exact finite_shared_not_five
    rw [f.shared_card_split]
    exact hf f.triangular
  rw [fan_ordinary_card n L hL hn tri ht p (mem_filter.mp hp).1 D (by omega) hi hp,
    fan_core_card n L hL hn tri ht p (mem_filter.mp hp).1 D (by omega) hi hp] at hfinite
  exact hfinite

theorem closed_extremal_capacity {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (P : Finset Point) (sub : P⊆core n L)
    (closed : SharedCoreClosed n L (fun a => ofPredicate n L (tri a) hL (ht a)) P)
    (triples : ∀ p∈P, (supports n L p).card=3) :
    let G := fun a => ofPredicate n L (tri a) hL (ht a)
    3*(P.filter (fun p => ordinaryDegree n L G p=3)).card≤
      ∑ p∈P.filter (fun p => ordinaryDegree n L G p≤1 ∧
        ordinaryDegree n L G p+coreDegree n L G p≤2), coreDegree n L G p := by
  classical
  let G := fun a => ofPredicate n L (tri a) hL (ht a)
  let E := P.filter (fun p => ordinaryDegree n L G p=3)
  let B := P.filter (fun p => ordinaryDegree n L G p≤1 ∧
    ordinaryDegree n L G p+coreDegree n L G p≤2)
  have hInd (e : Edge) (he : e∈twoCoreEdges n L G) : (e∩E).card≤1 := by
    apply card_le_one.mpr
    intro p hp q hq
    by_contra hpq
    obtain ⟨hpe,hpE⟩ := mem_inter.mp hp
    obtain ⟨hqe,hqE⟩ := mem_inter.mp hq
    obtain ⟨hpP,hpOrd⟩ := mem_filter.mp hpE
    obtain ⟨hqP,hqOrd⟩ := mem_filter.mp hqE
    have hpair : e={p,q} := by
      apply Eq.symm
      apply eq_of_subset_of_card_le
      · intro x hx
        rcases mem_insert.mp hx with hx|hx
        · simpa only [hx] using hpe
        · simpa only [mem_singleton.mp hx] using hqe
      · rw [card_pair hpq,used_edge_card G (mem_filter.mp (mem_sdiff.mp he).1).1]
    exact certificate_cap_heavy_not_adjacent n L hL hn tri hi ht p q (sub hpP) (sub hqP)
      ⟨triples p hpP,Or.inl hpOrd⟩ ⟨triples q hqP,Or.inl hqOrd⟩
      (by simpa only [hpair] using he)
  have hEdge (e : Edge) (he : e∈twoCoreEdges n L G) : (e∩E).card≤(e∩B).card := by
    by_cases hempty : e∩E=∅
    · simp [hempty]
    · obtain ⟨p,hp⟩ := nonempty_iff_ne_empty.mpr hempty
      obtain ⟨hpe,hpE⟩ := mem_inter.mp hp
      obtain ⟨hpP,hpOrd⟩ := mem_filter.mp hpE
      obtain ⟨q,hqp,heq⟩ := pair_of_card_two_of_mem e p hpe
        (used_edge_card G (mem_filter.mp (mem_sdiff.mp he).1).1)
      have hqe : q∈e := by simp [heq]
      have hqP : q∈P := closed e he p hpe hpP hqe
      have poor := UpperOpenMathMarkedPoverty.certificate_extremal_neighbor_sum
        n L hL hn tri hi ht p q (sub hpP) (sub hqP) (triples p hpP) (triples q hqP)
        hpOrd (by simpa only [heq] using he)
      have hqB : q∈B := mem_filter.mpr ⟨hqP,poor⟩
      have hpos : 1≤(e∩B).card := card_pos.mpr ⟨q,mem_inter.mpr ⟨hqe,hqB⟩⟩
      exact (hInd e he).trans hpos
  have count : (∑ p∈E, coreDegree n L G p)≤∑ p∈B, coreDegree n L G p := by
    change (∑ p∈E, ((twoCoreEdges n L G).filter (fun e => p∈e)).card)≤
      ∑ p∈B, ((twoCoreEdges n L G).filter (fun e => p∈e)).card
    rw [UpperOpenMathCoreDoubleCount.endpoint_double_count,
      UpperOpenMathCoreDoubleCount.endpoint_double_count]
    exact sum_le_sum hEdge
  have source : (∑ p∈E, coreDegree n L G p)=3*E.card := by
    calc
      _=∑ _p∈E, 3 := by
        apply sum_congr rfl
        intro p hp
        obtain ⟨hpP,hpOrd⟩ := mem_filter.mp hp
        have hext : 2*(supports n L p).card-3≤ordinaryDegree n L G p := by
          rw [triples p hpP,hpOrd]
        exact UpperOpenMathSupportedCores.certificate_extremal_neighbor_count
          n L hL hn tri hi ht p (sub hpP) hext
      _=3*E.card := by simp [Nat.mul_comm]
  change 3*E.card≤∑ p∈B, coreDegree n L G p
  rw [← source]
  exact count

theorem finite_weight_discharge {β : Type*} [DecidableEq β]
    (P : Finset β) (a d : β → ℕ)
    (ha : ∀ p∈P, a p≤3) (hd : ∀ p∈P, d p≤3)
    (hfive : ∀ p∈P, a p+d p≠5)
    (capacity : 3*(P.filter (fun p => a p=3)).card≤
      ∑ p∈P.filter (fun p => a p≤1 ∧ a p+d p≤2), d p) :
    0≤∑ p∈P, (6-2*(a p : ℤ)-d p) ∧
    ((∑ p∈P, (6-2*(a p : ℤ)-d p))=0 → ∀ p∈P, a p=2 ∧ d p=2) := by
  classical
  let E := P.filter (fun p => a p=3)
  let B := P.filter (fun p => a p≤1 ∧ a p+d p≤2)
  have esub : E⊆P := filter_subset _ _
  have bsub : B⊆P := filter_subset _ _
  have hPoint (p : β) (hp : p∈P) :
      -(3 : ℤ)*(if p∈E then 1 else 0)+(if p∈B then (d p : ℤ)+2 else 0)≤6-2*(a p : ℤ)-d p := by
    have hpa := ha p hp
    have hpd := hd p hp
    have hpf := hfive p hp
    by_cases he : p∈E
    · have hap := (mem_filter.mp he).2
      have hb : p∉B := by intro hh; have hh' := (mem_filter.mp hh).2.1; omega
      simp only [he,hb,ite_true,ite_false]
      omega
    · have hap : a p≠3 := fun hh => he (mem_filter.mpr ⟨hp,hh⟩)
      by_cases hb : p∈B
      · have hab := (mem_filter.mp hb).2
        simp only [he,hb,ite_true,ite_false]
        omega
      · simp only [he,hb,ite_true,ite_false]
        omega
  have hSum := sum_le_sum hPoint
  have hecount : (∑ p∈P, (if p∈E then (1 : ℤ) else 0))=E.card := by
    simp [inter_eq_right.mpr esub]
  have hbcount : (∑ p∈P, (if p∈B then (d p : ℤ)+2 else 0))=
      (∑ p∈B, (d p : ℤ))+2*B.card := by
    rw [← sum_filter,filter_mem_eq_inter,inter_eq_right.mpr bsub,sum_add_distrib]
    simp [mul_comm]
  simp only [sum_add_distrib,← mul_sum] at hSum
  rw [hecount,hbcount] at hSum
  have hc : 3*(E.card : ℤ)≤∑ p∈B, (d p : ℤ) := by exact_mod_cast capacity
  have hbpos : 0≤(B.card : ℤ) := by positivity
  constructor
  · linarith
  · intro hz
    have hbzero : B=∅ := card_eq_zero.mp (by omega)
    have hezero : E=∅ := by
      simp only [hbzero,sum_empty] at hc
      exact card_eq_zero.mp (by omega)
    have hap (p : β) (hp : p∈P) : a p≠3 := by
      intro hh
      have hpe : p∈E := mem_filter.mpr ⟨hp,hh⟩
      rw [hezero] at hpe
      exact notMem_empty p hpe
    have hnonneg (p : β) (hp : p∈P) : (0 : ℤ)≤6-2*(a p : ℤ)-d p := by
      have hpa := ha p hp
      have hpd := hd p hp
      have hpf := hfive p hp
      have hpe := hap p hp
      omega
    have hzero := (sum_eq_zero_iff_of_nonneg hnonneg).mp hz
    intro p hp
    have hpa := ha p hp
    have hpd := hd p hp
    have hpf := hfive p hp
    have hpe := hap p hp
    have hw := hzero p hp
    omega

theorem certificate_closed_degree_three_cost_pos {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (P : Finset Point) (sub : P⊆core n L) (nonempty : P.Nonempty)
    (closed : SharedCoreClosed n L (fun a => ofPredicate n L (tri a) hL (ht a)) P)
    (triples : ∀ p∈P, (supports n L p).card=3)
    (degree : ∀ p∈P, coreDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) p≤3) :
    1≤componentCost n L (fun a => ofPredicate n L (tri a) hL (ht a)) P := by
  classical
  let G := fun a => ofPredicate n L (tri a) hL (ht a)
  let a := ordinaryDegree n L G
  let d := coreDegree n L G
  change 1≤componentCost n L G P
  have ha (p : Point) (hp : p∈P) : a p≤3 := by
    have hh := certificate_local_fan_bound n L hL hn tri hi ht p (sub hp)
    rw [triples p hp] at hh
    exact hh
  have hfive (p : Point) (hp : p∈P) : a p+d p≠5 :=
    certificate_triple_not_five n L hL hn tri hi ht p (sub hp) (triples p hp)
  have capacity := closed_extremal_capacity n L hL hn tri hi ht P sub closed triples
  have discharge := finite_weight_discharge P a d ha degree hfive capacity
  have hsum : (∑ p∈P, (d p : ℤ))=2*((componentEdges n L G P).card : ℤ) := by
    exact_mod_cast closed_degree_sum n L G P closed
  have hr : (∑ p∈P, (supports n L p).card*((supports n L p).card-2 : ℤ))=
      3*(P.card : ℤ) := by
    calc
      _=∑ _p∈P, (3 : ℤ) := by
        apply sum_congr rfl
        intro p hp
        rw [triples p hp]
        norm_num
      _=3*(P.card : ℤ) := by simp [mul_comm]
  have identity : 2*componentCost n L G P=∑ p∈P, (6-2*(a p : ℤ)-d p) := by
    rw [componentCost,hr]
    simp only [sum_sub_distrib,← mul_sum,sum_const,nsmul_eq_mul]
    rw [hsum]
    ring
  have nonneg : 0≤componentCost n L G P := by nlinarith [discharge.1]
  have nozero : componentCost n L G P≠0 := by
    intro hz
    have hw : (∑ p∈P, (6-2*(a p : ℤ)-d p))=0 := by rw [← identity,hz]; ring
    have rigid (p : Point) (hp : p∈P) :
        (supports n L p).card=3 ∧ a p=2 ∧ d p=2 :=
      ⟨triples p hp,discharge.2 hw p hp⟩
    exact UpperOpenMathTwoTwoCore.certificate_closed_two_two_impossible
      n L hL hn tri hi ht P sub nonempty closed rigid
  omega

theorem certificate_degree_three_component_bound {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (triples : ∀ p∈core n L, (supports n L p).card=3)
    (degree : ∀ p∈core n L, coreDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) p≤3) :
    let G := fun a => ofPredicate n L (tri a) hL (ht a)
    3*(Fintype.card α : ℤ)+(UpperEdgeInventory.edges n L\usedEdges G).card+
      coreComponentCount n L G≤(n : ℤ)*(n-2) := by
  classical
  let G := fun a => ofPredicate n L (tri a) hL (ht a)
  have hEach (s : (coreGraph n L G).ConnectedComponent) (hs : s∈components n L G) :
      (1 : ℤ)≤componentCost n L G (componentVertices n L G s) :=
    certificate_closed_degree_three_cost_pos n L hL hn tri hi ht (componentVertices n L G s)
      (component_subset n L G s) (component_nonempty n L G s)
      (component_closed n L hL tri ht s)
      (fun p hp => triples p (component_subset n L G s hp))
      (fun p hp => degree p (component_subset n L G s hp))
  have hSum := sum_le_sum hEach
  simp only [sum_const,nsmul_eq_mul,mul_one,components_card] at hSum
  have hid := certificate_component_cost_identity n L hL hn tri hi ht
  dsimp only at hid
  change 3*(Fintype.card α : ℤ)+(UpperEdgeInventory.edges n L\usedEdges G).card+
    coreComponentCount n L G≤(n : ℤ)*(n-2)
  linarith

#print axioms finite_shared_not_five
#print axioms certificate_triple_not_five
#print axioms closed_extremal_capacity
#print axioms finite_weight_discharge
#print axioms certificate_closed_degree_three_cost_pos
#print axioms certificate_degree_three_component_bound
end Kobon.UpperOpenMathTripleDegreeThree
