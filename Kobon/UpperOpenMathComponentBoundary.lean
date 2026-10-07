import Kobon.UpperOpenMathFullSharing
import Kobon.UpperOpenMathCoreHull
import Kobon.UpperOpenMathRayResources
import Kobon.UpperOpenMathMixedCapBudget

/-! Every actual shared-core component pays for its own convex boundary.
The bounds have no restriction on multiplicity, core degree, or fan types. -/
namespace Kobon.UpperOpenMathComponentBoundary
open Cells FanGeometry UpperVertexBudget UpperTriangleIncidence UpperSharedIncidence
  UpperCoreExtraction UpperOpenMathCapHeavyTriples UpperOpenMathCoreComponents
  UpperOpenMathFullSharing UpperOpenMathCoreHull UpperOpenMathRayResources Finset
open scoped BigOperators
set_option maxHeartbeats 1000000

noncomputable def componentBoundaryCount {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (G : α → TriangleGeometry) : ℕ :=
  ∑ s∈components n L G, (boundary (componentVertices n L G s)).card

noncomputable def componentBoundaryMinimum {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (G : α → TriangleGeometry) : ℕ :=
  ∑ s∈components n L G, min (componentVertices n L G s).card 3

theorem component_boundary_minimum_le {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (G : α → TriangleGeometry) :
    componentBoundaryMinimum n L G≤componentBoundaryCount n L G :=
  sum_le_sum (fun s _ => boundary_card _)

theorem components_le_boundary_minimum {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (G : α → TriangleGeometry) :
    coreComponentCount n L G≤componentBoundaryMinimum n L G := by
  classical
  have each (s : (coreGraph n L G).ConnectedComponent) (hs : s∈components n L G) :
      1≤min (componentVertices n L G s).card 3 := by
    have pos := card_pos.mpr (component_nonempty n L G s)
    omega
  have total := sum_le_sum each
  simp only [sum_const,nsmul_eq_mul,mul_one,components_card] at total
  exact total

theorem certificate_closed_supported_sharing_gap {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (P : Finset Point) (sub : P⊆core n L)
    (closed : SharedCoreClosed n L (fun a => ofPredicate n L (tri a) hL (ht a)) P)
    (c : Point) (hc : c∈P) (support : HasSupport P c) :
    ordinaryDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) c+
      coreDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) c≤2*(supports n L c).card-2 := by
  classical
  have coreC := sub hc
  have hr := core_multiplicity n L hL coreC
  letI : NeZero (2*(supports n L c).card) := ⟨by omega⟩
  let D := UpperOpenMathRadialOrder.atPoint n L hL hn c
  let f := UpperOpenMathActualFans.fan n L hL hn tri ht c (mem_filter.mp coreC).1 D (by omega)
  have gap := shared_gap (by omega : 1≤(supports n L c).card) f
  rw [← f.shared_card_split,
    UpperOpenMathActualFans.fan_ordinary_card n L hL hn tri ht c (mem_filter.mp coreC).1 D (by omega) hi coreC,
    UpperOpenMathActualFans.fan_core_card n L hL hn tri ht c (mem_filter.mp coreC).1 D (by omega) hi coreC] at gap
  rcases gap with full|less
  · obtain ⟨w,hw,valid,hpos⟩ := support
    obtain ⟨q,hq,edge,negative⟩ := certificate_full_sharing_neighbors_surround n L hL hn tri hi ht c coreC w hw valid full
    have qP := closed {c,q} edge c (by simp) hc (by simp : q∈({c,q} : Finset Point))
    exact False.elim (not_lt_of_ge (hpos q qP) negative)
  · exact less

theorem certificate_closed_boundary_budget {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (P : Finset Point) (sub : P⊆core n L)
    (closed : SharedCoreClosed n L (fun a => ofPredicate n L (tri a) hL (ht a)) P) :
    let G := fun a => ofPredicate n L (tri a) hL (ht a)
    (∑ p∈P, ((ordinaryDegree n L G p : ℤ)+coreDegree n L G p))+
      2*(boundary P).card≤2*∑ p∈P, ((supports n L p).card : ℤ) := by
  classical
  let G := fun a => ofPredicate n L (tri a) hL (ht a)
  have each (p : Point) (hp : p∈P) :
      ((ordinaryDegree n L G p : ℤ)+coreDegree n L G p)+
        2*(if HasSupport P p then 1 else 0 : ℤ)≤2*(supports n L p).card := by
    by_cases supp : HasSupport P p
    · have localGap := certificate_closed_supported_sharing_gap n L hL hn tri hi ht P sub closed p hp supp
      have r := core_multiplicity n L hL (sub hp)
      have castGap : ((ordinaryDegree n L G p : ℤ)+coreDegree n L G p)≤
          ((2*(supports n L p).card-2 : ℕ) : ℤ) := by exact_mod_cast localGap
      rw [Nat.cast_sub (by omega : 2≤2*(supports n L p).card)] at castGap
      simp only [Nat.cast_mul,Nat.cast_ofNat,if_pos supp] at castGap ⊢
      omega
    · have localBound := UpperOpenMathMixedCapBudget.certificate_local_combined_degree n L hL hn tri hi ht p (sub hp)
      have castBound : ((ordinaryDegree n L G p : ℤ)+coreDegree n L G p)≤2*(supports n L p).card := by exact_mod_cast localBound
      simp only [if_neg supp,mul_zero,add_zero]
      exact castBound
  have total := sum_le_sum each
  have count : (∑ p∈P, (if HasSupport P p then (1 : ℤ) else 0))=(boundary P).card := by
    simp [boundary,sum_ite]
  simp only [sum_add_distrib,← mul_sum,count] at total
  simpa only [sum_add_distrib] using total

theorem certificate_component_boundary_budget {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a)) :
    let G := fun a => ofPredicate n L (tri a) hL (ht a)
    ((oneCoreEdges n L G).card : ℤ)+2*(twoCoreEdges n L G).card+
      2*componentBoundaryCount n L G≤2*∑ p∈core n L, ((supports n L p).card : ℤ) := by
  classical
  let G := fun a => ofPredicate n L (tri a) hL (ht a)
  have each (s : (coreGraph n L G).ConnectedComponent) (hs : s∈components n L G) :=
    certificate_closed_boundary_budget n L hL hn tri hi ht (componentVertices n L G s)
      (component_subset n L G s) (component_closed n L hL tri ht s)
  have total := sum_le_sum each
  simp only [sum_add_distrib,← mul_sum,component_sum] at total
  have ordinarySum := UpperOpenMathCoreDoubleCount.one_core_incidence_sum n L hL tri hi ht
  have ordinarySumZ : (∑ p∈core n L, (ordinaryDegree n L G p : ℤ))=(oneCoreEdges n L G).card := by exact_mod_cast ordinarySum
  have coreSum := closed_degree_sum n L G (core n L) (by
    intro e he p hpe hp q hqe
    exact (mem_powersetCard.mp (UpperCoreCombinatorics.core_edge_subset n L hL tri ht he)).1 hqe)
  have allEdges : componentEdges n L G (core n L)=twoCoreEdges n L G := by
    apply filter_eq_self.mpr
    intro e he
    exact (mem_powersetCard.mp (UpperCoreCombinatorics.core_edge_subset n L hL tri ht he)).1
  rw [allEdges] at coreSum
  have coreSumZ : (∑ p∈core n L, (coreDegree n L G p : ℤ))=2*(twoCoreEdges n L G).card := by exact_mod_cast coreSum
  have boundarySum : (∑ s∈components n L G,
      ((boundary (componentVertices n L G s)).card : ℤ))=componentBoundaryCount n L G := by
    exact_mod_cast (rfl : (∑ s∈components n L G, (boundary (componentVertices n L G s)).card)=componentBoundaryCount n L G)
  rw [ordinarySumZ,coreSumZ,boundarySum] at total
  exact total

theorem certificate_component_boundary_resources {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a)) :
    let G := fun a => ofPredicate n L (tri a) hL (ht a)
    2*componentBoundaryCount n L G≤
      UpperOpenMathCoreCapacity.nonsharedCoreIncidences n L G+coreEndRays n L := by
  classical
  let G := fun a => ofPredicate n L (tri a) hL (ht a)
  have budget := certificate_component_boundary_budget n L hL hn tri hi ht
  have exactResources := certificate_ray_resource_identity n L hL hn tri hi ht
  dsimp only at budget exactResources ⊢
  have exactZ : ((oneCoreEdges n L G).card : ℤ)+2*(twoCoreEdges n L G).card+
      UpperOpenMathCoreCapacity.nonsharedCoreIncidences n L G+coreEndRays n L=
        2*∑ p∈core n L, ((supports n L p).card : ℤ) := by exact_mod_cast exactResources
  have boundZ : 2*(componentBoundaryCount n L G : ℤ)≤
      UpperOpenMathCoreCapacity.nonsharedCoreIncidences n L G+coreEndRays n L := by linarith
  exact_mod_cast boundZ

#print axioms certificate_closed_boundary_budget
#print axioms certificate_component_boundary_budget
#print axioms certificate_component_boundary_resources
end Kobon.UpperOpenMathComponentBoundary
