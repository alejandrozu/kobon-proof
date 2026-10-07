import Kobon.UpperOpenMathAntipodalStarWeights
import Kobon.UpperOpenMathMarkedCurvatureBound

/-! Each actual shared-core component of order at most five costs at least
one unit of Tamura defect in an all-triple arrangement. -/
namespace Kobon.UpperOpenMathFiveCoreComponents
open Cells FanGeometry UpperFan UpperVertexBudget UpperTriangleIncidence UpperSharedIncidence
  UpperCoreExtraction UpperOpenMathCapHeavyTriples UpperOpenMathCoreComponents
  UpperOpenMathAntipodalTwoCapChart UpperOpenMathAntipodalStarWeights
  UpperOpenMathMarkedPorts UpperOpenMathMarkedCurvature Finset
open scoped BigOperators
set_option maxHeartbeats 1000000

theorem closed_degree_bound {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L)
    (tri : α → Triple) (ht : ∀ a, TrianglePredicate n L (tri a))
    (P : Finset Point)
    (closed : SharedCoreClosed n L (fun a => ofPredicate n L (tri a) hL (ht a)) P)
    (p : Point) (hp : p∈P) :
    coreDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) p≤P.card-1 := by
  classical
  let G := fun a => ofPredicate n L (tri a) hL (ht a)
  let E := (twoCoreEdges n L G).filter (fun e => p∈e)
  have bound := UpperOpenMathCoreDegree.pair_inventory_degree_bound P E (by
    intro e he
    obtain ⟨he,hpe⟩ := mem_filter.mp he
    have used := (mem_filter.mp (mem_sdiff.mp he).1).1
    exact ⟨used_edge_card G used,fun q hq => closed e he p hpe hp hq⟩) p hp
  have idempotent : E.filter (fun e => p∈e)=E := filter_eq_self.mpr (fun e he => (mem_filter.mp he).2)
  rw [idempotent] at bound
  exact bound

theorem antipodal_star_cost_positive {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (triples : ∀ p∈core n L, (supports n L p).card=3)
    (f : UpperFan.Sectors n 3 L)
    (data : AntipodalData (fun a => ofPredicate n L (tri a) hL (ht a)) f)
    (P : Finset Point) (sub : P⊆core n L) (hc : f.center∈P) (small : P.card≤5)
    (closed : SharedCoreClosed n L (fun a => ofPredicate n L (tri a) hL (ht a)) P)
    (centerA : ordinaryDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) f.center=2)
    (centerD : coreDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) f.center=4) :
    1≤componentCost n L (fun a => ofPredicate n L (tri a) hL (ht a)) P := by
  classical
  let G := fun a => ofPredicate n L (tri a) hL (ht a)
  let W := fun p => (6-2*(ordinaryDegree n L G p : ℤ)-coreDegree n L G p)
  have first := certificate_first_pair_weight n L hL hn tri hi ht triples f data P sub hc small closed centerA
  let g := UpperOpenMathRotation.Sectors.shift f 3
  have dg := shift_three_data G f data
  have second := certificate_first_pair_weight n L hL hn tri hi ht triples g dg P sub hc small closed centerA
  have i4 : (3 : ZMod (2*3))+1=4 := by decide
  have i5 : (3 : ZMod (2*3))+2=5 := by decide
  change 2≤W (f.point 1)+W (f.point 2) at first
  change 2≤W (f.point (3+1))+W (f.point (3+2)) at second
  rw [i4,i5] at second
  have star := closed_star_eq G f data.toFullData P hc small closed
  have no : f.center∉f.coreShared.image f.point := by
    intro h
    obtain ⟨z,_,hz⟩ := mem_image.mp h
    exact data.noncentral z hz
  have sumW : (∑ p∈P, W p)=W f.center+W (f.point 1)+W (f.point 2)+W (f.point 4)+W (f.point 5) := by
    rw [star,sum_insert no,sum_image]
    · rw [data.core_eq]
      rw [sum_insert (by decide),sum_insert (by decide),sum_insert (by decide),sum_singleton]
      ring
    · intro a _ b _ he
      exact data.injective he
  have wc : W f.center=-2 := by dsimp [W]; rw [centerA,centerD]; norm_num
  have identity := UpperOpenMathTripleCurvature.closed_curvature_identity n L G P closed
    (fun p hp => triples p (sub hp))
  change 2*componentCost n L G P=(∑ p∈P, W p) at identity
  rw [sumW,wc] at identity
  change 1≤componentCost n L G P
  linarith

theorem certificate_closed_five_cost_positive {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (triples : ∀ p∈core n L, (supports n L p).card=3)
    (P : Finset Point) (sub : P⊆core n L) (nonempty : P.Nonempty) (small : P.card≤5)
    (closed : SharedCoreClosed n L (fun a => ofPredicate n L (tri a) hL (ht a)) P) :
    1≤componentCost n L (fun a => ofPredicate n L (tri a) hL (ht a)) P := by
  classical
  let G := fun a => ofPredicate n L (tri a) hL (ht a)
  by_cases unpaid : ∃ p∈P, ordinaryDegree n L G p=2 ∧ coreDegree n L G p=4 ∧
      markedCount n L hL hn tri ht p=0
  · obtain ⟨p,hp,ap,dp,mp⟩ := unpaid
    obtain ⟨f,fc,data⟩ := certificate_antipodal_chart n L hL hn tri hi ht p (sub hp) (triples p (sub hp)) ap dp mp
    apply antipodal_star_cost_positive n L hL hn tri hi ht triples f data P sub
      (by simpa only [fc] using hp) small closed
    · simpa only [fc] using ap
    · simpa only [fc] using dp
  · have zero : unpaidOn n L hL hn tri ht P=0 := by
      unfold unpaidOn
      change (∑ p∈P, UpperOpenMathMarkedCurvatureWeights.unpaidWeight
        (ordinaryDegree n L G p) (coreDegree n L G p) (markedCount n L hL hn tri ht p))=0
      apply sum_eq_zero
      intro p hp
      have degree := closed_degree_bound n L hL tri ht P closed p hp
      change coreDegree n L G p≤P.card-1 at degree
      have no24 : ¬(ordinaryDegree n L G p=2 ∧ coreDegree n L G p=4 ∧
          markedCount n L hL hn tri ht p=0) := fun hh => unpaid ⟨p,hp,hh⟩
      unfold UpperOpenMathMarkedCurvatureWeights.unpaidWeight
      split_ifs <;> omega
    have bound := UpperOpenMathMarkedCurvatureBound.certificate_closed_marked_cost_pos
      n L hL hn tri hi ht triples P sub nonempty closed
    rw [zero,add_zero] at bound
    exact bound

theorem certificate_five_core_component_bound {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (triples : ∀ p∈core n L, (supports n L p).card=3)
    (small : ∀ s∈components n L (fun a => ofPredicate n L (tri a) hL (ht a)),
      (componentVertices n L (fun a => ofPredicate n L (tri a) hL (ht a)) s).card≤5) :
    let G := fun a => ofPredicate n L (tri a) hL (ht a)
    3*(Fintype.card α : ℤ)+(UpperEdgeInventory.edges n L\usedEdges G).card+
      coreComponentCount n L G≤(n : ℤ)*(n-2) := by
  classical
  let G := fun a => ofPredicate n L (tri a) hL (ht a)
  have each (s : (coreGraph n L G).ConnectedComponent) (hs : s∈components n L G) :
      (1 : ℤ)≤componentCost n L G (componentVertices n L G s) :=
    certificate_closed_five_cost_positive n L hL hn tri hi ht triples (componentVertices n L G s)
      (component_subset n L G s) (component_nonempty n L G s) (small s hs) (component_closed n L hL tri ht s)
  have summed := sum_le_sum each
  simp only [sum_const,nsmul_eq_mul,mul_one,components_card] at summed
  have identity := certificate_component_cost_identity n L hL hn tri hi ht
  dsimp only at identity
  change 3*(Fintype.card α : ℤ)+(UpperEdgeInventory.edges n L\usedEdges G).card+
    coreComponentCount n L G≤(n : ℤ)*(n-2)
  linarith

theorem certificate_five_total_core_bound {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (triples : ∀ p∈core n L, (supports n L p).card=3) (small : (core n L).card≤5) :
    let G := fun a => ofPredicate n L (tri a) hL (ht a)
    3*(Fintype.card α : ℤ)+(UpperEdgeInventory.edges n L\usedEdges G).card+
      coreComponentCount n L G≤(n : ℤ)*(n-2) := by
  apply certificate_five_core_component_bound n L hL hn tri hi ht triples
  intro s _
  exact (card_le_card (component_subset n L _ s)).trans small

#print axioms certificate_closed_five_cost_positive
#print axioms certificate_five_core_component_bound
#print axioms certificate_five_total_core_bound
end Kobon.UpperOpenMathFiveCoreComponents
