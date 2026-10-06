import Kobon.UpperOpenMathSingleSourceCurvature
import Kobon.UpperOpenMathAntipodalThreeNeighbors

/-! Adaptive actual component bounds, and a geometric seven-core criterion
for the stronger single-source inequality. -/
namespace Kobon.UpperOpenMathSingleSourceComponents
open Cells FanGeometry UpperVertexBudget UpperTriangleIncidence UpperSharedIncidence
  UpperCoreExtraction UpperOpenMathCapHeavyTriples UpperOpenMathCoreComponents
  UpperOpenMathMarkedPorts UpperOpenMathAntipodalTwoCapChart
  UpperOpenMathAntipodalSameNeighbors UpperOpenMathAntipodalThreeNeighbors
  UpperOpenMathClosedHalfCurvature Finset
open scoped BigOperators
set_option maxHeartbeats 1000000

theorem certificate_seven_core_single_source {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (triples : ∀ p∈core n L, (supports n L p).card=3)
    (P : Finset Point) (sub : P⊆core n L)
    (closed : SharedCoreClosed n L (fun a => ofPredicate n L (tri a) hL (ht a)) P)
    (small : P.card≤7) :
    (P.filter (fun p => ordinaryDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) p=2 ∧
      coreDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) p=4 ∧ markedCount n L hL hn tri ht p=0)).card≤1 := by
  classical
  let G := fun a => ofPredicate n L (tri a) hL (ht a)
  let A := P.filter (fun p => ordinaryDegree n L G p=2 ∧ coreDegree n L G p=4 ∧ markedCount n L hL hn tri ht p=0)
  change A.card≤1
  apply card_le_one.mpr
  intro c hc d hd
  by_contra ne
  obtain ⟨hcP,ac,dc,mc⟩ := mem_filter.mp hc
  obtain ⟨hdP,ad,dd,md⟩ := mem_filter.mp hd
  have hcA : AntipodalCore n L hL hn tri ht c := ⟨sub hcP,triples c (sub hcP),ac,dc,mc⟩
  have hdA : AntipodalCore n L hL hn tri ht d := ⟨sub hdP,triples d (sub hdP),ad,dd,md⟩
  have cardNeighbors (p : Point) (hp : AntipodalCore n L hL hn tri ht p) :
      (coreNeighbors n L G p).card=4 := by
    obtain ⟨hp,rp,ap,dp,mp⟩ := hp
    obtain ⟨f,fp,df⟩ := certificate_antipodal_chart n L hL hn tri hi ht p hp rp ap dp mp
    have eq := chart_outer_eq_neighbors n L G f df
    rw [fp] at eq
    rw [←eq,card_image_of_injective _ df.injective,df.core_card]
  have cc := cardNeighbors c hcA
  have cd := cardNeighbors d hdA
  have ci := certificate_common_neighbor_card_le_two n L hL hn tri hi ht c d hcA hdA ne
  change (coreNeighbors n L G c∩coreNeighbors n L G d).card≤2 at ci
  have outside (p : Point) (hpP : p∈P) (q : Point) (hq : q∈coreNeighbors n L G p) : q∈P := by
    exact closed {p,q} (mem_filter.mp hq).2 p (by simp) hpP (by simp)
  have noself (p : Point) : p∉coreNeighbors n L G p := by
    intro hp
    have card := used_edge_card G (mem_filter.mp (mem_sdiff.mp (mem_filter.mp hp).2).1).1
    simp at card
  have noedge : ({c,d} : Edge)∉twoCoreEdges n L G := by
    intro edge
    exact UpperOpenMathAntipodalAdjacency.certificate_unmarked_full_not_adjacent n L hL hn tri hi ht triples
      c d (sub hcP) (sub hdP) ac ad dc dd mc md edge
  have unionSub : coreNeighbors n L G c∪coreNeighbors n L G d⊆(P.erase c).erase d := by
    intro q hq
    rcases mem_union.mp hq with hq|hq
    · apply mem_erase.mpr
      refine ⟨?_,mem_erase.mpr ⟨?_,outside c hcP q hq⟩⟩
      · intro eq; subst q; exact noedge (mem_filter.mp hq).2
      · intro eq; subst q; exact noself c hq
    · apply mem_erase.mpr
      refine ⟨?_,mem_erase.mpr ⟨?_,outside d hdP q hq⟩⟩
      · intro eq; subst q; exact noself d hq
      · intro eq; subst q; exact noedge (by simpa only [pair_comm] using (mem_filter.mp hq).2)
  have cu := card_le_card unionSub
  have hdErase : d∈P.erase c := mem_erase.mpr ⟨Ne.symm ne,hdP⟩
  rw [card_erase_of_mem hdErase,card_erase_of_mem hcP] at cu
  have unionCount := card_union_add_card_inter (coreNeighbors n L G c) (coreNeighbors n L G d)
  omega

noncomputable def singleSourceLowerOn {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L)
    (tri : α → Triple) (ht : ∀ a, TrianglePredicate n L (tri a)) (P : Finset Point) : ℤ :=
  let G := fun a => ofPredicate n L (tri a) hL (ht a)
  let B := (P.filter (fun p => ordinaryDegree n L G p=1 ∧ coreDegree n L G p=5)).card
  let E := (P.filter (fun p => ordinaryDegree n L G p=3)).card
  let Q := (P.filter (fun p => ordinaryDegree n L G p=2 ∧ coreDegree n L G p=1)).card
  (3*(E : ℤ)+2*(Q : ℤ)-(B : ℤ)+1)/2

noncomputable def adaptiveLowerOn {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (ht : ∀ a, TrianglePredicate n L (tri a)) (P : Finset Point) : ℤ := by
  classical
  let G := fun a => ofPredicate n L (tri a) hL (ht a)
  let A := (P.filter (fun p => ordinaryDegree n L G p=2 ∧ coreDegree n L G p=4 ∧ markedCount n L hL hn tri ht p=0)).card
  exact if A≤1 then max (hybridGainLowerOn n L hL hn tri ht P) (singleSourceLowerOn n L hL tri ht P)
    else hybridGainLowerOn n L hL hn tri ht P

theorem certificate_closed_single_source_lower {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (triples : ∀ p∈core n L, (supports n L p).card=3)
    (P : Finset Point) (sub : P⊆core n L)
    (closed : SharedCoreClosed n L (fun a => ofPredicate n L (tri a) hL (ht a)) P)
    (small : (P.filter (fun p => ordinaryDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) p=2 ∧
      coreDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) p=4 ∧ markedCount n L hL hn tri ht p=0)).card≤1) :
    singleSourceLowerOn n L hL tri ht P≤componentCost n L (fun a => ofPredicate n L (tri a) hL (ht a)) P := by
  classical
  let G := fun a => ofPredicate n L (tri a) hL (ht a)
  let B := (P.filter (fun p => ordinaryDegree n L G p=1 ∧ coreDegree n L G p=5)).card
  let E := (P.filter (fun p => ordinaryDegree n L G p=3)).card
  let Q := (P.filter (fun p => ordinaryDegree n L G p=2 ∧ coreDegree n L G p=1)).card
  have gain := UpperOpenMathSingleSourceCurvature.certificate_closed_single_source_gain n L hL hn tri hi ht triples P sub closed small
  change 0≤2*componentCost n L G P+(B : ℤ)-3*(E : ℤ)-2*(Q : ℤ) at gain
  change (3*(E : ℤ)+2*(Q : ℤ)-(B : ℤ)+1)/2≤componentCost n L G P
  omega

theorem certificate_closed_adaptive_lower {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (triples : ∀ p∈core n L, (supports n L p).card=3)
    (P : Finset Point) (sub : P⊆core n L) (nonempty : P.Nonempty)
    (closed : SharedCoreClosed n L (fun a => ofPredicate n L (tri a) hL (ht a)) P) :
    adaptiveLowerOn n L hL hn tri ht P≤componentCost n L (fun a => ofPredicate n L (tri a) hL (ht a)) P := by
  classical
  have base := certificate_closed_hybrid_gain_lower n L hL hn tri hi ht triples P sub nonempty closed
  unfold adaptiveLowerOn
  dsimp only
  split_ifs with small
  · exact max_le base (certificate_closed_single_source_lower n L hL hn tri hi ht triples P sub closed small)
  · exact base

theorem certificate_adaptive_component_defect {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (triples : ∀ p∈core n L, (supports n L p).card=3) :
    let G := fun a => ofPredicate n L (tri a) hL (ht a)
    (UpperEdgeInventory.edges n L\usedEdges G).card+
      (∑ s∈components n L G,adaptiveLowerOn n L hL hn tri ht (componentVertices n L G s))≤
      (n : ℤ)*(n-2)-3*Fintype.card α := by
  classical
  let G := fun a => ofPredicate n L (tri a) hL (ht a)
  have each (s : (coreGraph n L G).ConnectedComponent) (hs : s∈components n L G) :=
    certificate_closed_adaptive_lower n L hL hn tri hi ht triples (componentVertices n L G s)
      (component_subset n L G s) (component_nonempty n L G s) (component_closed n L hL tri ht s)
  have summed := sum_le_sum each
  have identity := certificate_component_cost_identity n L hL hn tri hi ht
  dsimp only at identity ⊢
  linarith

theorem certificate_seven_component_defect {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (triples : ∀ p∈core n L, (supports n L p).card=3)
    (small : ∀ s∈components n L (fun a => ofPredicate n L (tri a) hL (ht a)),
      (componentVertices n L (fun a => ofPredicate n L (tri a) hL (ht a)) s).card≤7) :
    let G := fun a => ofPredicate n L (tri a) hL (ht a)
    (UpperEdgeInventory.edges n L\usedEdges G).card+
      (∑ s∈components n L G,singleSourceLowerOn n L hL tri ht (componentVertices n L G s))≤
      (n : ℤ)*(n-2)-3*Fintype.card α := by
  classical
  let G := fun a => ofPredicate n L (tri a) hL (ht a)
  have each (s : (coreGraph n L G).ConnectedComponent) (hs : s∈components n L G) :=
    certificate_closed_single_source_lower n L hL hn tri hi ht triples (componentVertices n L G s)
      (component_subset n L G s) (component_closed n L hL tri ht s)
      (certificate_seven_core_single_source n L hL hn tri hi ht triples (componentVertices n L G s)
        (component_subset n L G s) (component_closed n L hL tri ht s) (small s hs))
  have summed := sum_le_sum each
  have identity := certificate_component_cost_identity n L hL hn tri hi ht
  dsimp only at identity ⊢
  linarith

theorem adaptive_dominates {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (ht : ∀ a, TrianglePredicate n L (tri a)) (P : Finset Point) :
    hybridGainLowerOn n L hL hn tri ht P≤adaptiveLowerOn n L hL hn tri ht P := by
  classical
  unfold adaptiveLowerOn
  dsimp only
  split_ifs
  · exact le_max_left _ _
  · exact le_rfl

#print axioms certificate_seven_core_single_source
#print axioms certificate_adaptive_component_defect
#print axioms certificate_seven_component_defect
#print axioms adaptive_dominates
end Kobon.UpperOpenMathSingleSourceComponents
