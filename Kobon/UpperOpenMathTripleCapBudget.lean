import Kobon.UpperOpenMathTripleOrdinaryBudget

/-!
# Partial cap fans give an additional global ordinary-edge saving

Let e count ordinary-degree-three triple cores, and b count triple cores
with ordinary degree two and core degree one. Their shared-core edges are
marked on both sides by ordinary caps. The actual target has total sharing
degree at most two. Discharging therefore proves `D1 + 2e + b <= 2q`.
All graph incidences and local fan hypotheses are extracted from the actual
chosen certified triangles.
-/
namespace Kobon.UpperOpenMathTripleCapBudget
open Cells FanGeometry UpperVertexBudget UpperTriangleIncidence UpperSharedIncidence
  UpperCoreExtraction UpperOpenMathCapHeavyTriples Finset
open scoped BigOperators

theorem finite_discharge {β : Type*} [DecidableEq β]
    (C : Finset β) (a d : β → ℕ) (p : ℕ)
    (bound : ∀ c∈C, a c≤3)
    (capacity : 3*(C.filter (fun c => a c=3)).card+p≤
      ∑ c∈C.filter (fun c => a c≤1 ∧ a c+d c≤2), d c) :
    (∑ c∈C, a c)+2*(C.filter (fun c => a c=3)).card+p≤2*C.card := by
  classical
  let E := C.filter (fun c => a c=3)
  let B := C.filter (fun c => a c≤1 ∧ a c+d c≤2)
  have hPoint (c : β) (hc : c∈C) :
      (a c : ℤ)≤2+(if c∈E then 1 else 0)-(if c∈B then d c else 0) := by
    have hb := bound c hc
    by_cases he : c∈E
    · have ha := (mem_filter.mp he).2
      have hnot : c∉B := by intro hh; have hl := (mem_filter.mp hh).2.1; omega
      simp only [he,hnot,ite_true,ite_false]
      omega
    · have ha : a c≠3 := fun hh => he (mem_filter.mpr ⟨hc,hh⟩)
      by_cases hB : c∈B
      · have hl := (mem_filter.mp hB).2.2
        simp only [he,hB,ite_true,ite_false]
        omega
      · simp only [he,hB,ite_true,ite_false]
        omega
  have hSum := sum_le_sum hPoint
  have hEsub : E⊆C := filter_subset _ _
  have hBsub : B⊆C := filter_subset _ _
  have hEcount : (∑ c∈C, if c∈E then (1 : ℤ) else 0)=E.card := by
    simp [inter_eq_right.mpr hEsub]
  have hBfilter : C.filter (fun c => c∈B)=B := by
    rw [filter_mem_eq_inter,inter_eq_right.mpr hBsub]
  have hBcount : (∑ c∈C, if c∈B then (d c : ℤ) else 0)=∑ c∈B, (d c : ℤ) := by
    rw [← sum_filter,hBfilter]
  simp only [sum_sub_distrib,sum_add_distrib,sum_const,nsmul_eq_mul,Nat.cast_ite,Nat.cast_zero] at hSum
  rw [hEcount,hBcount] at hSum
  have capacityZ : (3 : ℤ)*E.card+p≤∑ c∈B, (d c : ℤ) := by exact_mod_cast capacity
  have finalZ : (∑ c∈C, (a c : ℤ))+2*E.card+p≤2*C.card := by omega
  exact_mod_cast finalZ

theorem certificate_triple_cap_budget {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (triples : ∀ c∈core n L, (supports n L c).card=3) :
    let G := fun a => ofPredicate n L (tri a) hL (ht a)
    (oneCoreEdges n L G).card+
      2*((core n L).filter (fun c => ordinaryDegree n L G c=3)).card+
      ((core n L).filter (fun c => ordinaryDegree n L G c=2 ∧ coreDegree n L G c=1)).card≤
      2*(core n L).card := by
  classical
  let G := fun a => ofPredicate n L (tri a) hL (ht a)
  let C := core n L
  let E := C.filter (fun c => ordinaryDegree n L G c=3)
  let P := C.filter (fun c => ordinaryDegree n L G c=2 ∧ coreDegree n L G c=1)
  let A := E∪P
  let B := C.filter (fun c => ordinaryDegree n L G c≤1 ∧
    ordinaryDegree n L G c+coreDegree n L G c≤2)
  have hAcore (c : Point) (hc : c∈A) : c∈C := by
    rcases mem_union.mp hc with hc|hc <;> exact (mem_filter.mp hc).1
  have hAcap (c : Point) (hc : c∈A) : CapHeavy n L G c := by
    refine ⟨triples c (hAcore c hc),?_⟩
    rcases mem_union.mp hc with hc|hc
    · exact Or.inl (mem_filter.mp hc).2
    · exact Or.inr (mem_filter.mp hc).2
  have hInd (e : Edge) (he : e∈twoCoreEdges n L G) : (e∩A).card≤1 := by
    apply card_le_one.mpr
    intro p hp q hq
    by_contra hpq
    obtain ⟨hpe,hpA⟩ := mem_inter.mp hp
    obtain ⟨hqe,hqA⟩ := mem_inter.mp hq
    have hpair : e={p,q} := by
      apply Eq.symm
      apply eq_of_subset_of_card_le
      · intro x hx
        simp only [mem_insert,mem_singleton] at hx
        rcases hx with rfl|rfl <;> assumption
      · rw [card_pair hpq,used_edge_card G (mem_filter.mp (mem_sdiff.mp he).1).1]
    exact certificate_cap_heavy_not_adjacent n L hL hn tri hi ht p q
      (hAcore p hpA) (hAcore q hqA) (hAcap p hpA) (hAcap q hqA)
      (by simpa only [hpair] using he)
  have hEdge (e : Edge) (he : e∈twoCoreEdges n L G) : (e∩A).card≤(e∩B).card := by
    by_cases hEmpty : e∩A=∅
    · simp [hEmpty]
    · obtain ⟨p,hp⟩ := nonempty_iff_ne_empty.mpr hEmpty
      obtain ⟨hpEdge,hpA⟩ := mem_inter.mp hp
      have hpC := hAcore p hpA
      have hused := (mem_filter.mp (mem_sdiff.mp he).1).1
      obtain ⟨q,hqp,heq⟩ := UpperOpenMathActualFans.pair_of_card_two_of_mem e p hpEdge (used_edge_card G hused)
      have hqEdge : q∈e := by simp [heq]
      have hqC : q∈C := mem_filter.mpr
        ⟨UpperEdgeInventory.certificate_side_vertices n L hL tri ht hused hqEdge,
          twoCore_endpoints n L G he q hqEdge⟩
      have poor := UpperOpenMathMarkedPoverty.certificate_cap_heavy_neighbor_sum n L hL hn tri hi ht
        p q hpC hqC (triples p hpC) (triples q hqC) (hAcap p hpA).2
        (by simpa only [heq] using he)
      have hB : q∈B := mem_filter.mpr ⟨hqC,poor⟩
      have hpos : 1≤(e∩B).card := card_pos.mpr ⟨q,mem_inter.mpr ⟨hqEdge,hB⟩⟩
      exact (hInd e he).trans hpos
  have hCount : (∑ p∈A, coreDegree n L G p)≤∑ p∈B, coreDegree n L G p := by
    change (∑ p∈A, ((twoCoreEdges n L G).filter (fun e => p∈e)).card)≤
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
  have hP : (∑ p∈P, coreDegree n L G p)=P.card := by
    calc
      _=∑ _p∈P, 1 := sum_congr rfl (fun p hp => (mem_filter.mp hp).2.2)
      _=P.card := by simp
  have disj : Disjoint E P := by
    apply disjoint_left.mpr
    intro p he hp
    have h3 := (mem_filter.mp he).2
    have h2 := (mem_filter.mp hp).2.1
    omega
  have hA : (∑ p∈A, coreDegree n L G p)=3*E.card+P.card := by
    rw [show A=E∪P from rfl,sum_union disj,hE,hP]
  have hCapacity : 3*E.card+P.card≤∑ p∈B, coreDegree n L G p := by
    rw [← hA]
    exact hCount
  have hBound (p : Point) (hp : p∈C) : ordinaryDegree n L G p≤3 := by
    have hb := UpperOpenMathActualFans.certificate_local_fan_bound n L hL hn tri hi ht p hp
    rw [triples p hp] at hb
    exact hb
  have hDischarge := finite_discharge C (ordinaryDegree n L G) (coreDegree n L G) P.card hBound hCapacity
  have hD := UpperOpenMathCoreDoubleCount.one_core_incidence_sum n L hL tri hi ht
  change (∑ p∈C, ordinaryDegree n L G p)=(oneCoreEdges n L G).card at hD
  rw [hD] at hDischarge
  exact hDischarge

theorem certificate_triple_cap_defect {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (triples : ∀ c∈core n L, (supports n L c).card=3) :
    let G := fun a => ofPredicate n L (tri a) hL (ht a)
    ((core n L).card : ℤ)+
      2*((core n L).filter (fun c => ordinaryDegree n L G c=3)).card+
      ((core n L).filter (fun c => ordinaryDegree n L G c=2 ∧ coreDegree n L G c=1)).card+
      (UpperEdgeInventory.edges n L\usedEdges G).card-(twoCoreEdges n L G).card≤
      (n : ℤ)*(n-2)-3*Fintype.card α := by
  classical
  let G := fun a => ofPredicate n L (tri a) hL (ht a)
  have hD := certificate_triple_cap_budget n L hL hn tri hi ht triples
  have hDZ : ((oneCoreEdges n L G).card : ℤ)+
      2*((core n L).filter (fun c => ordinaryDegree n L G c=3)).card+
      ((core n L).filter (fun c => ordinaryDegree n L G c=2 ∧ coreDegree n L G c=1)).card≤
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
  have hid := defect_identity n L hL hn tri hi ht
  rw [hS] at hid
  dsimp only at hid
  linarith

/-- If the shared-core graph has fewer edges than vertices, the exact
triangle count loses at least one, plus all exceptional and partial cap
penalties and every unused bounded elementary interval. -/
theorem certificate_sparse_core_strict_bound {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (triples : ∀ c∈core n L, (supports n L c).card=3)
    (sparse : (twoCoreEdges n L (fun a => ofPredicate n L (tri a) hL (ht a))).card<
      (core n L).card) :
    let G := fun a => ofPredicate n L (tri a) hL (ht a)
    3*(Fintype.card α : ℤ)+1+
      2*((core n L).filter (fun c => ordinaryDegree n L G c=3)).card+
      ((core n L).filter (fun c => ordinaryDegree n L G c=2 ∧ coreDegree n L G c=1)).card+
      (UpperEdgeInventory.edges n L\usedEdges G).card≤(n : ℤ)*(n-2) := by
  have h := certificate_triple_cap_defect n L hL hn tri hi ht triples
  dsimp only at h
  have hsZ : ((twoCoreEdges n L (fun a => ofPredicate n L (tri a) hL (ht a))).card : ℤ)<
      (core n L).card := by exact_mod_cast sparse
  omega

#print axioms certificate_triple_cap_budget
#print axioms certificate_triple_cap_defect
#print axioms certificate_sparse_core_strict_bound
end Kobon.UpperOpenMathTripleCapBudget
