import Kobon.UpperCoreLineIncidence
import Kobon.UpperCoreCombinatorics

/-!
# Actual shared-core endpoint capacity

An actual bounded elementary interval uses each vertex at most once as its
left endpoint and once as its right endpoint on a given arrangement line.
Summing these two injections proves the geometric capacity
`D1 + 2*D2 <= 2*I` for every chosen injective family of certified triangles.
There is no cyclic-fan ordering or fan-summation hypothesis in this result.
-/
namespace Kobon.UpperOpenMathCoreCapacity
open Cells FanGeometry UpperVertexBudget UpperTriangleIncidence
  UpperSharedIncidence UpperEdgeInventory UpperCoreExtraction
  UpperCoreLineIncidence Finset
open scoped BigOperators

theorem pair_inter_card {α : Type*} [DecidableEq α]
    (p q : α) (hpq : p≠q) (S : Finset α) :
    ({p,q}∩S).card=(if p∈S then 1 else 0)+(if q∈S then 1 else 0) := by
  by_cases hp : p∈S <;> by_cases hq : q∈S
  all_goals simp [hp,hq,hpq]

theorem path_endpoint_count (m : ℕ) (S : Finset (Fin m)) :
    (∑ k : Fin (m-1), (
      (if (⟨k.val,by have := k.isLt; omega⟩ : Fin m)∈S then 1 else 0)+
      (if (⟨k.val+1,by have := k.isLt; omega⟩ : Fin m)∈S then 1 else 0)))≤2*S.card := by
  classical
  let low : Fin (m-1) → Fin m := fun k => ⟨k.val,by have := k.isLt; omega⟩
  let high : Fin (m-1) → Fin m := fun k => ⟨k.val+1,by have := k.isLt; omega⟩
  have ilow : Function.Injective low := by
    intro a b he
    apply Fin.ext
    have hh := congrArg (fun x : Fin m => x.val) he
    exact hh
  have ihigh : Function.Injective high := by
    intro a b he
    apply Fin.ext
    have hh := congrArg (fun x : Fin m => x.val) he
    dsimp [high] at hh
    omega
  let A := univ.filter (fun k => low k∈S)
  let B := univ.filter (fun k => high k∈S)
  have hA : A.image low⊆S := by
    intro x hx
    obtain ⟨k,hk,rfl⟩ := mem_image.mp hx
    exact (mem_filter.mp hk).2
  have hB : B.image high⊆S := by
    intro x hx
    obtain ⟨k,hk,rfl⟩ := mem_image.mp hx
    exact (mem_filter.mp hk).2
  have hla := card_le_card hA
  have hlb := card_le_card hB
  rw [card_image_of_injective _ ilow] at hla
  rw [card_image_of_injective _ ihigh] at hlb
  have hc : (∑ k : Fin (m-1),
      ((if low k∈S then (1 : ℕ) else 0)+(if high k∈S then 1 else 0)))=A.card+B.card := by
    simp [sum_add_distrib,sum_boole,A,B]
  change (∑ k : Fin (m-1),
    ((if low k∈S then 1 else 0)+(if high k∈S then 1 else 0)))≤_
  rw [hc]
  omega

theorem interval_core_card (n : ℕ) (L : ℕ → Line ℝ) (i : Fin n)
    (k : Fin ((coordinates n L i).card-1)) :
    (intervalEdge n L i k∩core n L).card=
      (if (⟨k.val,by have := k.isLt; omega⟩ : Fin (coordinates n L i).card)
        ∈coreIndices n L i then 1 else 0)+
      (if (⟨k.val+1,by have := k.isLt; omega⟩ : Fin (coordinates n L i).card)
        ∈coreIndices n L i then 1 else 0) := by
  classical
  have hne : orderedPoint n L i ⟨k.val,by have := k.isLt; omega⟩≠
      orderedPoint n L i ⟨k.val+1,by have := k.isLt; omega⟩ := by
    intro he
    have hh := congrArg (fun x : Fin (coordinates n L i).card => x.val)
      (orderedPoint_injective n L i he)
    change k.val=k.val+1 at hh
    omega
  simp only [intervalEdge,pair_inter_card _ _ hne,coreIndices,mem_filter,
    mem_univ,true_and]

theorem line_core_endpoint_capacity (n : ℕ) (L : ℕ → Line ℝ)
    (hL : NoParallel n L) (hn : 2≤n) (i : Fin n) :
    (∑ e∈lineEdges n L i, (e∩core n L).card)≤2*(onCoreLine n L i).card := by
  classical
  rw [lineEdges,sum_image]
  · simp_rw [interval_core_card]
    have hh := path_endpoint_count (coordinates n L i).card (coreIndices n L i)
    rw [coreIndices_card n L hL hn i] at hh
    exact hh
  · intro a _ b _ he
    exact intervalEdge_injective n L i he

/-- The endpoint capacity is extracted from actual elementary intervals,
including intervals unused by the chosen triangle family. -/
theorem inventory_core_endpoint_capacity (n : ℕ) (L : ℕ → Line ℝ)
    (hL : NoParallel n L) (hn : 2≤n) :
    (∑ e∈edges n L, (e∩core n L).card)≤
      2*(∑ p∈core n L, (supports n L p).card) := by
  classical
  rw [edges,sum_biUnion (lineEdges_pairwise_disjoint n L hL hn)]
  have hh := sum_le_sum (s:=univ) (fun i _ => line_core_endpoint_capacity n L hL hn i)
  rw [← mul_sum,core_line_incidence] at hh
  exact hh

theorem oneCore_core_card {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    {e : Edge} (he : e∈oneCoreEdges n L (fun a => ofPredicate n L (tri a) hL (ht a))) :
    (e∩core n L).card=1 := by
  classical
  obtain ⟨p,q,hpq,rfl,hpo,hqc⟩ := certificate_oneCore_classification n L hL tri hi ht he
  have hpc : p∉core n L := by
    intro hp
    exact (mem_filter.mp hp).2 hpo
  simp [hpc,hqc]

theorem twoCore_core_card {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L)
    (tri : α → Triple) (ht : ∀ a, TrianglePredicate n L (tri a))
    {e : Edge} (he : e∈twoCoreEdges n L (fun a => ofPredicate n L (tri a) hL (ht a))) :
    (e∩core n L).card=2 := by
  classical
  let geometry := fun a => ofPredicate n L (tri a) hL (ht a)
  have hused := (mem_filter.mp (mem_sdiff.mp he).1).1
  have hsub : e⊆core n L := by
    intro p hp
    exact mem_filter.mpr ⟨certificate_side_vertices n L hL tri ht hused hp,
      twoCore_endpoints n L geometry he p hp⟩
  rw [inter_eq_left.mpr hsub]
  exact used_edge_card geometry hused

/-- Full geometric shared-ray capacity, with all counts taken from the
actual arrangement and actual chosen certified triangle family. -/
theorem certificate_shared_core_capacity {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a)) :
    let geometry := fun a => ofPredicate n L (tri a) hL (ht a)
    (oneCoreEdges n L geometry).card+2*(twoCoreEdges n L geometry).card≤
      2*(∑ p∈core n L, (supports n L p).card) := by
  classical
  let geometry := fun a => ofPredicate n L (tri a) hL (ht a)
  let A := oneCoreEdges n L geometry
  let B := twoCoreEdges n L geometry
  have hab : Disjoint A B := by
    apply disjoint_left.mpr
    intro e ha hb
    exact (mem_sdiff.mp hb).2 ha
  have hsub : A∪B⊆edges n L := by
    intro e he
    apply certificate_sides_subset n L hL hn tri ht
    rcases mem_union.mp he with he|he
    · exact (mem_filter.mp (mem_filter.mp he).1).1
    · exact (mem_filter.mp (mem_sdiff.mp he).1).1
  have hc : (∑ e∈A∪B, (e∩core n L).card)=A.card+2*B.card := by
    rw [sum_union hab]
    have hA : (∑ e∈A, (e∩core n L).card)=A.card := by
      calc
        _=∑ _e∈A, 1 := sum_congr rfl (fun e he => oneCore_core_card n L hL tri hi ht he)
        _=A.card := by simp
    have hB : (∑ e∈B, (e∩core n L).card)=2*B.card := by
      calc
        _=∑ _e∈B, 2 := sum_congr rfl (fun e he => twoCore_core_card n L hL tri ht he)
        _=2*B.card := by simp [Nat.mul_comm]
    rw [hA,hB]
  have hle : (∑ e∈A∪B, (e∩core n L).card)≤
      ∑ e∈edges n L, (e∩core n L).card :=
    sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.zero_le _)
  rw [hc] at hle
  exact hle.trans (inventory_core_endpoint_capacity n L hL hn)

theorem shared_core_endpoint_count {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a)) :
    let geometry := fun a => ofPredicate n L (tri a) hL (ht a)
    (∑ e∈sharedEdges geometry, (e∩core n L).card)=
      (oneCoreEdges n L geometry).card+2*(twoCoreEdges n L geometry).card := by
  classical
  let geometry := fun a => ofPredicate n L (tri a) hL (ht a)
  let A := oneCoreEdges n L geometry
  let B := twoCoreEdges n L geometry
  have he : A∪B=sharedEdges geometry := by
    ext e
    simp only [A,B,twoCoreEdges,mem_union,mem_sdiff]
    have hs : e∈oneCoreEdges n L geometry → e∈sharedEdges geometry :=
      fun h => (mem_filter.mp h).1
    tauto
  have hab : Disjoint A B := by
    apply disjoint_left.mpr
    intro e ha hb
    exact (mem_sdiff.mp hb).2 ha
  change (∑ e∈sharedEdges geometry, (e∩core n L).card)=A.card+2*B.card
  rw [← he,sum_union hab]
  have hA : (∑ e∈A, (e∩core n L).card)=A.card := by
    calc
      _=∑ _e∈A, 1 := sum_congr rfl (fun e he => oneCore_core_card n L hL tri hi ht he)
      _=A.card := by simp
  have hB : (∑ e∈B, (e∩core n L).card)=2*B.card := by
    calc
      _=∑ _e∈B, 2 := sum_congr rfl (fun e he => twoCore_core_card n L hL tri ht he)
      _=2*B.card := by simp [Nat.mul_comm]
  rw [hA,hB]

noncomputable def nonsharedCoreIncidences {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (geometry : α → TriangleGeometry) : ℕ := by
  classical
  exact ∑ e∈edges n L\sharedEdges geometry, (e∩core n L).card

/-- Retaining every nonshared elementary side incident to a core gives
an explicit stronger capacity. The new term counts actual endpoints of
unused or singly used intervals; it is not a supplied numerical slack. -/
theorem certificate_capacity_with_nonshared {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a)) :
    let geometry := fun a => ofPredicate n L (tri a) hL (ht a)
    (oneCoreEdges n L geometry).card+2*(twoCoreEdges n L geometry).card+
      nonsharedCoreIncidences n L geometry≤
      2*(∑ p∈core n L, (supports n L p).card) := by
  classical
  let geometry := fun a => ofPredicate n L (tri a) hL (ht a)
  have hsub : sharedEdges geometry⊆edges n L := by
    intro e he
    exact certificate_sides_subset n L hL hn tri ht (mem_filter.mp he).1
  have hsum := sum_sdiff hsub (f:=fun e : Edge => (e∩core n L).card)
  have hid := shared_core_endpoint_count n L hL tri hi ht
  have hcap := inventory_core_endpoint_capacity n L hL hn
  change (∑ e∈sharedEdges geometry, (e∩core n L).card)=
    (oneCoreEdges n L geometry).card+2*(twoCoreEdges n L geometry).card at hid
  change (oneCoreEdges n L geometry).card+2*(twoCoreEdges n L geometry).card+
    (∑ e∈edges n L\sharedEdges geometry, (e∩core n L).card)≤_
  omega

#print axioms inventory_core_endpoint_capacity
#print axioms certificate_shared_core_capacity
#print axioms certificate_capacity_with_nonshared
end Kobon.UpperOpenMathCoreCapacity
