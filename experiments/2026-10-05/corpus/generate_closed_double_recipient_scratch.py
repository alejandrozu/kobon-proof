"""Prepare a scratch componentwise actual double-recipient portfolio.

This never edits the stable release source set. Promotion is a separate step
after a complete standard-axiom replay and coordination with the root.
"""
from pathlib import Path
ROOT=Path(__file__).resolve().parents[3]
TARGET=ROOT/'research/openmath-seven-hour-2026-10-05/corpus/scratch/Kobon/UpperOpenMathClosedDoubleRecipientCurvature.lean'
TARGET.parent.mkdir(parents=True,exist_ok=True)
old=(ROOT/'Kobon/UpperOpenMathClosedHalfCurvature.lean').read_text(encoding='utf-8')
body=old.split('theorem certificate_closed_half_gain',1)[1].split(' := by\n',1)[1].split('  have result :=',1)[0]
start=body.index('  have narrow ');end=body.index('  have aPoor ',start)
body=body[:start]+body[end:]
small='''  have hsmall (p : Point) (hp : p∈P) (small : a p+d p≤4) : x p≤2 := by
    have global := UpperOpenMathNonfullAntipodalRecipients.certificate_nonfull_anti_degree_le_two
      n L hL hn tri hi ht triples p (sub hp) small
    have mono := degreeFrom_mono n L G A (unmarkedFullTwoCapSet n L hL hn tri ht) aGlobal p
    change degreeFrom n L G (unmarkedFullTwoCapSet n L hL hn tri ht) p≤2 at global
    have lower : degreeFrom n L G A p≤2 := mono.trans global
    dsimp [x]
    split_ifs <;> omega
'''
body=body.replace('  have hbalanced ',small+'  have hbalanced ',1)
prefix='''import Kobon.UpperOpenMathClosedHalfCurvature
import Kobon.UpperOpenMathDoubleRecipientCurvature

/-! Actual closed-component double-recipient charging and a componentwise
maximum with the existing strict/half-gain portfolio. -/
namespace Kobon.UpperOpenMathClosedDoubleRecipientCurvature
open Cells FanGeometry UpperVertexBudget UpperTriangleIncidence UpperSharedIncidence
  UpperCoreExtraction UpperOpenMathCapHeavyTriples UpperOpenMathCoreComponents
  UpperOpenMathMarkedPorts UpperOpenMathUnmarkedCrossResources
  UpperOpenMathAntipodalAdjacency UpperOpenMathTwoThirdCurvature Finset
open scoped BigOperators
set_option maxHeartbeats 1000000

noncomputable def closedRecipientCount {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (ht : ∀ a, TrianglePredicate n L (tri a))
    (P : Finset Point) (p : Point) : ℕ := by
  classical
  let G := fun a=>ofPredicate n L (tri a) hL (ht a)
  let A := P.filter (fun q=>ordinaryDegree n L G q=2 ∧ coreDegree n L G q=4 ∧
    markedCount n L hL hn tri ht q=0)
  exact if ordinaryDegree n L G p+coreDegree n L G p=6 then 0 else
    degreeFrom n L G A p

theorem certificate_closed_double_recipient_gain {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (triples : ∀ p∈core n L, (supports n L p).card=3)
    (P : Finset Point) (sub : P⊆core n L)
    (closed : SharedCoreClosed n L (fun a=>ofPredicate n L (tri a) hL (ht a)) P) :
    let G := fun a=>ofPredicate n L (tri a) hL (ht a)
    0≤2*componentCost n L G P+
      ((P.filter (fun p=>ordinaryDegree n L G p=1 ∧ coreDegree n L G p=5)).card : ℤ)+
      ((P.filter (fun p=>ordinaryDegree n L G p=1 ∧ coreDegree n L G p=3 ∧
        closedRecipientCount n L hL hn tri ht P p=2)).card : ℤ)-
      3*((P.filter (fun p=>ordinaryDegree n L G p=3)).card : ℤ)-
      2*((P.filter (fun p=>ordinaryDegree n L G p=2 ∧ coreDegree n L G p=1)).card : ℤ) := by
'''
tail='''  have result := UpperOpenMathDoubleRecipientWeights.finite_double_recipient_curvature_gain
    P a d m x ha had hfive hext hpartial hx hsmall hfull hbalanced capacity coneX
  have identity := UpperOpenMathTripleCurvature.closed_curvature_identity n L G P closed
    (fun p hp=>triples p (sub hp))
  change 0≤2*componentCost n L G P+
    ((P.filter (fun p=>a p=1 ∧ d p=5)).card : ℤ)+
    ((P.filter (fun p=>a p=1 ∧ d p=3 ∧ x p=2)).card : ℤ)-
    3*((P.filter (fun p=>a p=3)).card : ℤ)-
    2*((P.filter (fun p=>a p=2 ∧ d p=1)).card : ℤ)
  change 0≤(∑ p∈P,(6-2*(a p : ℤ)-d p))+
    ((P.filter (fun p=>a p=1 ∧ d p=5)).card : ℤ)+
    ((P.filter (fun p=>a p=1 ∧ d p=3 ∧ x p=2)).card : ℤ)-
    3*((P.filter (fun p=>a p=3)).card : ℤ)-
    2*((P.filter (fun p=>a p=2 ∧ d p=1)).card : ℤ) at result
  rw [←identity] at result
  exact result

noncomputable def doubleRecipientLowerOn {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (ht : ∀ a, TrianglePredicate n L (tri a)) (P : Finset Point) : ℤ :=
  let G := fun a=>ofPredicate n L (tri a) hL (ht a)
  let B := (P.filter (fun p=>ordinaryDegree n L G p=1 ∧ coreDegree n L G p=5)).card
  let J := (P.filter (fun p=>ordinaryDegree n L G p=1 ∧ coreDegree n L G p=3 ∧
    closedRecipientCount n L hL hn tri ht P p=2)).card
  let E := (P.filter (fun p=>ordinaryDegree n L G p=3)).card
  let Q := (P.filter (fun p=>ordinaryDegree n L G p=2 ∧ coreDegree n L G p=1)).card
  (3*(E : ℤ)+2*(Q : ℤ)-(B : ℤ)-(J : ℤ)+1)/2

noncomputable def hybridDoubleLowerOn {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (ht : ∀ a, TrianglePredicate n L (tri a)) (P : Finset Point) : ℤ :=
  max (UpperOpenMathClosedHalfCurvature.hybridGainLowerOn n L hL hn tri ht P)
    (doubleRecipientLowerOn n L hL hn tri ht P)

theorem certificate_closed_double_lower {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (triples : ∀ p∈core n L, (supports n L p).card=3)
    (P : Finset Point) (sub : P⊆core n L)
    (closed : SharedCoreClosed n L (fun a=>ofPredicate n L (tri a) hL (ht a)) P) :
    doubleRecipientLowerOn n L hL hn tri ht P≤
      componentCost n L (fun a=>ofPredicate n L (tri a) hL (ht a)) P := by
  have h := certificate_closed_double_recipient_gain n L hL hn tri hi ht triples P sub closed
  dsimp only [doubleRecipientLowerOn] at h ⊢
  omega

theorem certificate_closed_hybrid_double_lower {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (triples : ∀ p∈core n L, (supports n L p).card=3)
    (P : Finset Point) (sub : P⊆core n L) (nonempty : P.Nonempty)
    (closed : SharedCoreClosed n L (fun a=>ofPredicate n L (tri a) hL (ht a)) P) :
    hybridDoubleLowerOn n L hL hn tri ht P≤
      componentCost n L (fun a=>ofPredicate n L (tri a) hL (ht a)) P := by
  apply max_le
  · exact UpperOpenMathClosedHalfCurvature.certificate_closed_hybrid_gain_lower
      n L hL hn tri hi ht triples P sub nonempty closed
  · exact certificate_closed_double_lower n L hL hn tri hi ht triples P sub closed

theorem certificate_hybrid_double_component_defect {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (triples : ∀ p∈core n L, (supports n L p).card=3) :
    let G := fun a=>ofPredicate n L (tri a) hL (ht a)
    (UpperEdgeInventory.edges n L\\usedEdges G).card+
      (∑ s∈components n L G,hybridDoubleLowerOn n L hL hn tri ht (componentVertices n L G s))≤
      (n : ℤ)*(n-2)-3*Fintype.card α := by
  classical
  let G := fun a=>ofPredicate n L (tri a) hL (ht a)
  have each (s : (coreGraph n L G).ConnectedComponent) (hs : s∈components n L G) :=
    certificate_closed_hybrid_double_lower n L hL hn tri hi ht triples (componentVertices n L G s)
      (component_subset n L G s) (component_nonempty n L G s) (component_closed n L hL tri ht s)
  have summed := sum_le_sum each
  have identity := certificate_component_cost_identity n L hL hn tri hi ht
  dsimp only at identity ⊢
  linarith

theorem hybrid_double_dominates {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (ht : ∀ a, TrianglePredicate n L (tri a)) (P : Finset Point) :
    UpperOpenMathClosedHalfCurvature.hybridGainLowerOn n L hL hn tri ht P≤
      hybridDoubleLowerOn n L hL hn tri ht P := le_max_left _ _

#print axioms certificate_closed_double_recipient_gain
#print axioms certificate_hybrid_double_component_defect
end Kobon.UpperOpenMathClosedDoubleRecipientCurvature
'''
TARGET.write_text(prefix+body+tail,encoding='utf-8')
print(str(TARGET.relative_to(ROOT)))
