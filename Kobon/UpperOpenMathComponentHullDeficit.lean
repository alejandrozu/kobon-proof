import Kobon.UpperOpenMathComponentBoundaryConsequences
import Kobon.UpperOpenMathGlobalFans

/-! Both ordinary sharing and total sharing pay at every component-hull
point. Their combined saving yields an unrestricted multiplicity-weighted
deficit bound and a strong consequence when no triple cores occur. -/
namespace Kobon.UpperOpenMathComponentHullDeficit
open Cells FanGeometry UpperVertexBudget UpperTriangleIncidence UpperSharedIncidence
  UpperCoreExtraction UpperOpenMathCapHeavyTriples UpperOpenMathCoreComponents
  UpperOpenMathComponentBoundary UpperOpenMathCoreHull Finset
open scoped BigOperators
set_option maxHeartbeats 1000000

theorem certificate_closed_supported_ordinary_gap {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (P : Finset Point) (sub : P⊆core n L)
    (closed : SharedCoreClosed n L (fun a => ofPredicate n L (tri a) hL (ht a)) P)
    (c : Point) (hc : c∈P) (support : HasSupport P c) :
    ordinaryDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) c≤2*(supports n L c).card-4 := by
  have hr := core_multiplicity n L hL (sub hc)
  by_contra h
  have extreme : 2*(supports n L c).card-3≤
      ordinaryDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) c := by omega
  obtain ⟨w,hw,valid,hpos⟩ := support
  obtain ⟨q,hq,edge,negative⟩ := UpperOpenMathSupportedCores.certificate_extremal_neighbors_surround
    n L hL hn tri hi ht c (sub hc) w hw valid extreme
  have qP := closed {c,q} edge c (by simp) hc (by simp : q∈({c,q} : Finset Point))
  exact not_lt_of_ge (hpos q qP) negative

theorem certificate_closed_ordinary_budget {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (P : Finset Point) (sub : P⊆core n L)
    (closed : SharedCoreClosed n L (fun a => ofPredicate n L (tri a) hL (ht a)) P) :
    let G := fun a => ofPredicate n L (tri a) hL (ht a)
    (∑ p∈P, (ordinaryDegree n L G p : ℤ))+3*P.card+(boundary P).card≤
      2*∑ p∈P, ((supports n L p).card : ℤ) := by
  classical
  let G := fun a => ofPredicate n L (tri a) hL (ht a)
  have each (p : Point) (hp : p∈P) :
      (ordinaryDegree n L G p : ℤ)+3+(if HasSupport P p then 1 else 0 : ℤ)≤
        2*(supports n L p).card := by
    have hr := core_multiplicity n L hL (sub hp)
    by_cases supp : HasSupport P p
    · have localBound := certificate_closed_supported_ordinary_gap n L hL hn tri hi ht P sub closed p hp supp
      have castBound : (ordinaryDegree n L G p : ℤ)≤((2*(supports n L p).card-4 : ℕ) : ℤ) := by exact_mod_cast localBound
      rw [Nat.cast_sub (by omega : 4≤2*(supports n L p).card)] at castBound
      simp only [Nat.cast_mul,Nat.cast_ofNat,if_pos supp] at castBound ⊢
      omega
    · have localBound := UpperOpenMathActualFans.certificate_local_fan_bound n L hL hn tri hi ht p (sub hp)
      have castBound : (ordinaryDegree n L G p : ℤ)≤((2*(supports n L p).card-3 : ℕ) : ℤ) := by exact_mod_cast localBound
      rw [Nat.cast_sub (by omega : 3≤2*(supports n L p).card)] at castBound
      simp only [Nat.cast_mul,Nat.cast_ofNat,if_neg supp] at castBound ⊢
      omega
  have total := sum_le_sum each
  have count : (∑ p∈P, (if HasSupport P p then (1 : ℤ) else 0))=(boundary P).card := by simp [boundary]
  simp only [sum_add_distrib,sum_const,nsmul_eq_mul,count,← mul_sum] at total
  simpa only [mul_comm] using total

theorem certificate_component_ordinary_budget {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a)) :
    let G := fun a => ofPredicate n L (tri a) hL (ht a)
    ((oneCoreEdges n L G).card : ℤ)+3*(core n L).card+componentBoundaryCount n L G≤
      2*∑ p∈core n L, ((supports n L p).card : ℤ) := by
  classical
  let G := fun a => ofPredicate n L (tri a) hL (ht a)
  have each (s : (coreGraph n L G).ConnectedComponent) (hs : s∈components n L G) :=
    certificate_closed_ordinary_budget n L hL hn tri hi ht (componentVertices n L G s)
      (component_subset n L G s) (component_closed n L hL tri ht s)
  have total := sum_le_sum each
  simp only [sum_add_distrib,← mul_sum,component_sum] at total
  have ordinarySum := UpperOpenMathCoreDoubleCount.one_core_incidence_sum n L hL tri hi ht
  have ordinarySumZ : (∑ p∈core n L, (ordinaryDegree n L G p : ℤ))=(oneCoreEdges n L G).card := by exact_mod_cast ordinarySum
  have verticesSumZ : (∑ s∈components n L G, ((componentVertices n L G s).card : ℤ))=(core n L).card := by
    exact_mod_cast component_vertices_sum n L G
  have boundarySum : (∑ s∈components n L G, ((boundary (componentVertices n L G s)).card : ℤ))=componentBoundaryCount n L G := by
    exact_mod_cast (rfl : (∑ s∈components n L G, (boundary (componentVertices n L G s)).card)=componentBoundaryCount n L G)
  rw [ordinarySumZ,verticesSumZ,boundarySum] at total
  exact total

theorem certificate_component_hull_deficit {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a)) :
    let G := fun a => ofPredicate n L (tri a) hL (ht a)
    2*(∑ p∈core n L, (supports n L p).card*((supports n L p).card-4 : ℤ))+
      3*(core n L).card+3*componentBoundaryCount n L G+
      2*(UpperEdgeInventory.edges n L\usedEdges G).card≤
        2*((n : ℤ)*(n-2)-3*Fintype.card α) := by
  classical
  let G := fun a => ofPredicate n L (tri a) hL (ht a)
  have ordinary := certificate_component_ordinary_budget n L hL hn tri hi ht
  have ray := UpperOpenMathComponentBoundaryConsequences.certificate_component_boundary_deficit n L hL hn tri hi ht
  have split : (∑ p∈core n L, (supports n L p).card*((supports n L p).card-3 : ℤ))=
      (∑ p∈core n L, (supports n L p).card*((supports n L p).card-4 : ℤ))+
      ∑ p∈core n L, ((supports n L p).card : ℤ) := by
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro p hp
    ring
  dsimp only at ordinary ray ⊢
  rw [split] at ray
  linarith

#print axioms certificate_component_ordinary_budget
#print axioms certificate_component_hull_deficit
end Kobon.UpperOpenMathComponentHullDeficit
