import Kobon.UpperOpenMathMixedAntipodalStar
import Kobon.UpperOpenMathNonAntipodalStarDegree
import Kobon.UpperOpenMathFiveCoreComponents
import Kobon.UpperOpenMathSmallCoreRigidity

/-! Shared-core components of order at most five pay their full mixed
multiplicity surplus without either exceptional correction. -/
namespace Kobon.UpperOpenMathMixedFiveCoreComponents
open Cells FanGeometry UpperFan UpperVertexBudget UpperTriangleIncidence UpperSharedIncidence
  UpperCoreExtraction UpperOpenMathCapHeavyTriples UpperOpenMathCoreComponents
  UpperOpenMathMixedStarWeights UpperOpenMathMixedDegreeThree UpperOpenMathMixedDegreeFour Finset
open scoped BigOperators
set_option maxHeartbeats 1000000

theorem certificate_mixed_nonantipodal_star_cost {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (f : UpperFan.Sectors n 3 L)
    (data : UpperOpenMathNonAntipodalTwoCapChart.NonAntipodalData (fun a => ofPredicate n L (tri a) hL (ht a)) f)
    (P : Finset Point) (sub : P⊆core n L) (hc : f.center∈P) (small : P.card≤5)
    (closed : SharedCoreClosed n L (fun a => ofPredicate n L (tri a) hL (ht a)) P)
    (rc : (supports n L f.center).card=3)
    (ac : ordinaryDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) f.center=2)
    (dc : coreDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) f.center=4) :
    1+higherSurplusOn n L P≤componentCost n L (fun a => ofPredicate n L (tri a) hL (ht a)) P := by
  classical
  let G := fun a => ofPredicate n L (tri a) hL (ht a)
  let W := mixedWeight n L G
  obtain ⟨degreeOne,degree⟩ := UpperOpenMathNonAntipodalStarDegree.certificate_outer_degrees
    n L hL tri ht f data P hc small closed
  have properties (z : ZMod (2*3)) (hz : z∈f.coreShared) :=
    certificate_weight_neighbor_full_two_cap n L hL hn tri hi ht (f.point z) f.center
      (data.core_endpoint z hz) (sub hc) rc ac dc
      (by simpa only [pair_comm] using UpperOpenMathNonAntipodalStarDegree.core_edge_of_label G f data z hz)
      (degree z hz)
  have one : (1 : ZMod (2*3))∈f.coreShared := by rw [data.core_eq]; simp
  have lower : 3≤W (f.point 1) := (properties 1 one).2.1 degreeOne
  have ge := single_le_sum (fun z hz => (properties z hz).1) one
  change W (f.point 1)≤∑ z∈f.coreShared, W (f.point z) at ge
  have star := UpperOpenMathNonAntipodalStarDegree.closed_star_eq G f data P hc small closed
  have no : f.center∉f.coreShared.image f.point := by
    intro h
    obtain ⟨z,_,hz⟩ := mem_image.mp h
    exact data.noncentral z hz
  have sumW : (∑ p∈P, W p)=W f.center+∑ z∈f.coreShared, W (f.point z) := by
    rw [star,sum_insert no,sum_image]
    intro a _ b _ h
    exact data.injective h
  have wc : W f.center=-2 := by dsimp [W,mixedWeight]; rw [rc,ac,dc]; norm_num
  have identity := mixed_weight_sum n L G P closed
  change (∑ p∈P, W p)=2*(componentCost n L G P-higherSurplusOn n L P) at identity
  rw [sumW,wc] at identity
  change 1+higherSurplusOn n L P≤componentCost n L G P
  omega

theorem certificate_closed_mixed_five_cost {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (P : Finset Point) (sub : P⊆core n L) (nonempty : P.Nonempty) (small : P.card≤5)
    (closed : SharedCoreClosed n L (fun a => ofPredicate n L (tri a) hL (ht a)) P) :
    1+higherSurplusOn n L P≤componentCost n L (fun a => ofPredicate n L (tri a) hL (ht a)) P := by
  classical
  let G := fun a => ofPredicate n L (tri a) hL (ht a)
  by_cases exceptional : ∃ p∈P, (supports n L p).card=3 ∧ ordinaryDegree n L G p=2 ∧ coreDegree n L G p=4
  · obtain ⟨p,hp,rp,ap,dp⟩ := exceptional
    by_cases zero : UpperOpenMathMarkedPorts.markedCount n L hL hn tri ht p=0
    · obtain ⟨f,fc,data⟩ := UpperOpenMathAntipodalTwoCapChart.certificate_antipodal_chart
        n L hL hn tri hi ht p (sub hp) rp ap dp zero
      exact UpperOpenMathMixedAntipodalStar.certificate_mixed_antipodal_star_cost n L hL hn tri hi ht
        f data P sub (by simpa only [fc] using hp) small closed
        (by simpa only [fc] using rp) (by simpa only [fc] using ap) (by simpa only [fc] using dp)
    · obtain ⟨f,fc,data⟩ := UpperOpenMathNonAntipodalTwoCapChart.certificate_nonantipodal_chart
        n L hL hn tri hi ht p (sub hp) rp ap dp zero
      exact certificate_mixed_nonantipodal_star_cost n L hL hn tri hi ht
        f data P sub (by simpa only [fc] using hp) small closed
        (by simpa only [fc] using rp) (by simpa only [fc] using ap) (by simpa only [fc] using dp)
  · have degree (p : Point) (hp : p∈P) : coreDegree n L G p≤4 := by
      have bound := UpperOpenMathFiveCoreComponents.closed_degree_bound n L hL tri ht P closed p hp
      change coreDegree n L G p≤P.card-1 at bound
      omega
    have zero : twoCapFullOn n L G P=0 := by
      unfold twoCapFullOn
      apply card_eq_zero.mpr
      apply eq_empty_iff_forall_notMem.mpr
      intro p hp
      obtain ⟨hpP,hpType⟩ := mem_filter.mp hp
      exact exceptional ⟨p,hpP,hpType⟩
    have bound := certificate_closed_mixed_degree_four_cost n L hL hn tri hi ht P sub nonempty closed degree
    change 1+higherSurplusOn n L P≤(twoCapFullOn n L G P : ℤ)+componentCost n L G P at bound
    rw [zero] at bound
    norm_num at bound
    exact bound

theorem certificate_mixed_five_component_bound {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (small : ∀ s∈components n L (fun a => ofPredicate n L (tri a) hL (ht a)),
      (componentVertices n L (fun a => ofPredicate n L (tri a) hL (ht a)) s).card≤5) :
    let G := fun a => ofPredicate n L (tri a) hL (ht a)
    3*(Fintype.card α : ℤ)+(UpperEdgeInventory.edges n L\usedEdges G).card+coreComponentCount n L G+
      higherSurplus n L≤(n : ℤ)*(n-2) := by
  classical
  let G := fun a => ofPredicate n L (tri a) hL (ht a)
  have each (s : (coreGraph n L G).ConnectedComponent) (hs : s∈components n L G) :=
    certificate_closed_mixed_five_cost n L hL hn tri hi ht (componentVertices n L G s)
      (component_subset n L G s) (component_nonempty n L G s) (small s hs) (component_closed n L hL tri ht s)
  have total := sum_le_sum each
  simp only [sum_add_distrib,sum_const,nsmul_eq_mul,mul_one,components_card,component_surplus_sum] at total
  have identity := certificate_component_cost_identity n L hL hn tri hi ht
  dsimp only at identity ⊢
  linarith

theorem certificate_mixed_five_total_core_bound {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a)) (small : (core n L).card≤5) :
    let G := fun a => ofPredicate n L (tri a) hL (ht a)
    3*(Fintype.card α : ℤ)+(UpperEdgeInventory.edges n L\usedEdges G).card+coreComponentCount n L G+
      higherSurplus n L≤(n : ℤ)*(n-2) := by
  apply certificate_mixed_five_component_bound n L hL hn tri hi ht
  intro s _
  exact (card_le_card (component_subset n L _ s)).trans small

#print axioms certificate_closed_mixed_five_cost
#print axioms certificate_mixed_five_component_bound
#print axioms certificate_mixed_five_total_core_bound

theorem certificate_mixed_five_component_perfect_simple {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (small : ∀ s∈components n L (fun a => ofPredicate n L (tri a) hL (ht a)),
      (componentVertices n L (fun a => ofPredicate n L (tri a) hL (ht a)) s).card≤5)
    (perfect : (n : ℤ)*(n-2)=3*Fintype.card α) : NoConcurrent n L := by
  classical
  let G := fun a => ofPredicate n L (tri a) hL (ht a)
  have bound := certificate_mixed_five_component_bound n L hL hn tri hi ht small
  change 3*(Fintype.card α : ℤ)+(UpperEdgeInventory.edges n L\usedEdges G).card+coreComponentCount n L G+
    higherSurplus n L≤(n : ℤ)*(n-2) at bound
  rw [perfect] at bound
  have hs := UpperOpenMathSmallCoreRigidity.higher_surplus_nonnegative n L
  have hu : (0 : ℤ)≤(UpperEdgeInventory.edges n L\usedEdges G).card := by positivity
  have zero : coreComponentCount n L G=0 := by omega
  exact (UpperOpenMathDegreeBudgets.core_empty_iff_simple n L hL).mp
    ((UpperOpenMathSmallCoreRigidity.component_count_zero_iff n L G).mp zero)

theorem certificate_mixed_five_total_perfect_simple {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a)) (small : (core n L).card≤5)
    (perfect : (n : ℤ)*(n-2)=3*Fintype.card α) : NoConcurrent n L := by
  apply certificate_mixed_five_component_perfect_simple n L hL hn tri hi ht _ perfect
  intro s _
  exact (card_le_card (component_subset n L _ s)).trans small

#print axioms certificate_mixed_five_component_perfect_simple
#print axioms certificate_mixed_five_total_perfect_simple
end Kobon.UpperOpenMathMixedFiveCoreComponents
