import Kobon.UpperOpenMathPartialCurvature
import Kobon.UpperOpenMathClosedPartialCurvature
import Kobon.UpperOpenMathSingleSourceComponents

/-! Counting consequences of an explicit no-two-antipodal-neighbors
condition. This helper module does not assume that geometric condition is
unconditionally true; a final actual wrapper must prove it. -/
namespace Kobon.UpperOpenMathN13Degree
open Cells FanGeometry UpperVertexBudget UpperTriangleIncidence UpperSharedIncidence
  UpperCoreExtraction UpperOpenMathCapHeavyTriples UpperOpenMathCoreComponents
  UpperOpenMathMarkedPorts UpperOpenMathUnmarkedCrossResources
  UpperOpenMathAntipodalAdjacency UpperOpenMathTwoThirdCurvature Finset
open scoped BigOperators
set_option maxHeartbeats 1000000

theorem degreeFrom_le_one_of_unique_neighbors {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (G : α → TriangleGeometry)
    (A : Finset Point) (p : Point) (pnot : p∉A)
    (unique : ∀ c∈A, ∀ d∈A, ({p,c} : Edge)∈twoCoreEdges n L G →
      ({p,d} : Edge)∈twoCoreEdges n L G → c=d) :
    degreeFrom n L G A p≤1 := by
  classical
  change ((twoCoreEdges n L G).filter (fun e=>p∈e ∧ (e∩A).Nonempty)).card≤1
  apply card_le_one.mpr
  intro e he f hf
  obtain ⟨he,hpe,c,hc⟩ := mem_filter.mp he
  obtain ⟨hf,hpf,d,hd⟩ := mem_filter.mp hf
  obtain ⟨hce,hcA⟩ := mem_inter.mp hc
  obtain ⟨hdf,hdA⟩ := mem_inter.mp hd
  have pair (e : Edge) (he : e∈twoCoreEdges n L G) (hpe : p∈e)
      (c : Point) (hcA : c∈A) (hce : c∈e) : e={p,c} := by
    have ne : p≠c := by intro eq; exact pnot (by simpa only [←eq] using hcA)
    apply Eq.symm
    apply eq_of_subset_of_card_le
    · intro q hq
      rcases mem_insert.mp hq with hq|hq
      · simpa only [hq] using hpe
      · simpa only [mem_singleton.mp hq] using hce
    · rw [card_pair ne,used_edge_card G (mem_filter.mp (mem_sdiff.mp he).1).1]
  have ep := pair e he hpe c hcA hce
  have fp := pair f hf hpf d hdA hdf
  have eq := unique c hcA d hdA (by simpa only [ep] using he) (by simpa only [fp] using hf)
  rw [ep,fp,eq]

def NoDoubleAntipodalRecipients {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (ht : ∀ a, TrianglePredicate n L (tri a)) : Prop :=
  let G := fun a=>ofPredicate n L (tri a) hL (ht a)
  let A := unmarkedFullTwoCapSet n L hL hn tri ht
  ∀ p∈core n L, ordinaryDegree n L G p=1 → coreDegree n L G p=3 →
    ∀ c∈A, ∀ d∈A, ({p,c} : Edge)∈twoCoreEdges n L G →
      ({p,d} : Edge)∈twoCoreEdges n L G → c=d

theorem certificate_n13_degree_le_one_of_unique {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (ht : ∀ a, TrianglePredicate n L (tri a))
    (unique : NoDoubleAntipodalRecipients n L hL hn tri ht)
    (p : Point) (hp : p∈core n L)
    (ap : ordinaryDegree n L (fun a=>ofPredicate n L (tri a) hL (ht a)) p=1)
    (dp : coreDegree n L (fun a=>ofPredicate n L (tri a) hL (ht a)) p=3) :
    degreeFrom n L (fun a=>ofPredicate n L (tri a) hL (ht a))
      (unmarkedFullTwoCapSet n L hL hn tri ht) p≤1 := by
  classical
  let G := fun a=>ofPredicate n L (tri a) hL (ht a)
  let A := unmarkedFullTwoCapSet n L hL hn tri ht
  have pnot : p∉A := by
    intro h
    have ap2 := (mem_filter.mp h).2.1
    change ordinaryDegree n L G p=2 at ap2
    change ordinaryDegree n L G p=1 at ap
    omega
  exact degreeFrom_le_one_of_unique_neighbors n L G A p pnot (unique p hp ap dp)

theorem certificate_n13_recipient_le_one_of_unique {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (ht : ∀ a, TrianglePredicate n L (tri a))
    (unique : NoDoubleAntipodalRecipients n L hL hn tri ht)
    (p : Point) (hp : p∈core n L)
    (ap : ordinaryDegree n L (fun a=>ofPredicate n L (tri a) hL (ht a)) p=1)
    (dp : coreDegree n L (fun a=>ofPredicate n L (tri a) hL (ht a)) p=3) :
    recipientCount n L hL hn tri ht p≤1 := by
  unfold recipientCount
  dsimp only
  rw [if_neg (by rw [ap,dp]; decide)]
  exact certificate_n13_degree_le_one_of_unique n L hL hn tri ht unique p hp ap dp

theorem certificate_recipient_correction_empty_of_unique {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (ht : ∀ a, TrianglePredicate n L (tri a))
    (unique : NoDoubleAntipodalRecipients n L hL hn tri ht) :
    (core n L).filter (fun p=>ordinaryDegree n L (fun a=>ofPredicate n L (tri a) hL (ht a)) p=1 ∧
      coreDegree n L (fun a=>ofPredicate n L (tri a) hL (ht a)) p=3 ∧ recipientCount n L hL hn tri ht p=2)=∅ := by
  classical
  apply eq_empty_iff_forall_notMem.mpr
  intro p hp
  obtain ⟨hp,ap,dp,xp⟩ := mem_filter.mp hp
  have bound := certificate_n13_recipient_le_one_of_unique n L hL hn tri ht unique p hp ap dp
  omega

theorem certificate_no_source_correction_of_unique {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (triples : ∀ p∈core n L, (supports n L p).card=3)
    (unique : NoDoubleAntipodalRecipients n L hL hn tri ht) :
    let G := fun a=>ofPredicate n L (tri a) hL (ht a)
    2*((n : ℤ)*(n-2)-3*Fintype.card α)+
      ((core n L).filter (fun p=>ordinaryDegree n L G p=1 ∧ coreDegree n L G p=5)).card≥
      2*(UpperEdgeInventory.edges n L\usedEdges G).card+
      3*((core n L).filter (fun p=>ordinaryDegree n L G p=3)).card+
      3*((core n L).filter (fun p=>ordinaryDegree n L G p=2 ∧ coreDegree n L G p=1)).card := by
  have result := UpperOpenMathPartialCurvature.certificate_partial_defect_bound n L hL hn tri hi ht triples
  dsimp only at result ⊢
  rw [certificate_recipient_correction_empty_of_unique n L hL hn tri ht unique,card_empty,Nat.cast_zero,add_zero] at result
  exact result

theorem certificate_closed_recipient_correction_empty_of_unique {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (ht : ∀ a, TrianglePredicate n L (tri a))
    (unique : NoDoubleAntipodalRecipients n L hL hn tri ht)
    (P : Finset Point) (sub : P⊆core n L) :
    P.filter (fun p=>ordinaryDegree n L (fun a=>ofPredicate n L (tri a) hL (ht a)) p=1 ∧
      coreDegree n L (fun a=>ofPredicate n L (tri a) hL (ht a)) p=3 ∧
      UpperOpenMathClosedPartialCurvature.closedRecipientCount n L hL hn tri ht P p=2)=∅ := by
  classical
  let G := fun a=>ofPredicate n L (tri a) hL (ht a)
  let A := P.filter (fun p=>ordinaryDegree n L G p=2 ∧ coreDegree n L G p=4 ∧ markedCount n L hL hn tri ht p=0)
  have aSub : A⊆unmarkedFullTwoCapSet n L hL hn tri ht := by
    intro p hp
    obtain ⟨hp,hpred⟩ := mem_filter.mp hp
    exact mem_filter.mpr ⟨sub hp,hpred⟩
  apply eq_empty_iff_forall_notMem.mpr
  intro p hp
  obtain ⟨hp,ap,dp,xp⟩ := mem_filter.mp hp
  have bound := certificate_n13_degree_le_one_of_unique n L hL hn tri ht unique p (sub hp) ap dp
  change (if ordinaryDegree n L G p+coreDegree n L G p=6 then 0 else degreeFrom n L G A p)=2 at xp
  rw [if_neg (by rw [ap,dp]; decide)] at xp
  have mono := degreeFrom_mono n L G A (unmarkedFullTwoCapSet n L hL hn tri ht) aSub p
  change degreeFrom n L G (unmarkedFullTwoCapSet n L hL hn tri ht) p≤1 at bound
  omega

theorem certificate_closed_no_source_gain_of_unique {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (triples : ∀ p∈core n L, (supports n L p).card=3)
    (unique : NoDoubleAntipodalRecipients n L hL hn tri ht)
    (P : Finset Point) (sub : P⊆core n L)
    (closed : SharedCoreClosed n L (fun a=>ofPredicate n L (tri a) hL (ht a)) P) :
    let G := fun a=>ofPredicate n L (tri a) hL (ht a)
    0≤2*componentCost n L G P+
      ((P.filter (fun p=>ordinaryDegree n L G p=1 ∧ coreDegree n L G p=5)).card : ℤ)-
      3*((P.filter (fun p=>ordinaryDegree n L G p=3)).card : ℤ)-
      3*((P.filter (fun p=>ordinaryDegree n L G p=2 ∧ coreDegree n L G p=1)).card : ℤ) := by
  have result := UpperOpenMathClosedPartialCurvature.certificate_closed_partial_recipient_gain
    n L hL hn tri hi ht triples P sub closed
  dsimp only at result ⊢
  rw [certificate_closed_recipient_correction_empty_of_unique n L hL hn tri ht unique P sub,
    card_empty,Nat.cast_zero,add_zero] at result
  exact result

noncomputable def sourceFreeLowerOn {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L)
    (tri : α → Triple) (ht : ∀ a, TrianglePredicate n L (tri a)) (P : Finset Point) : ℤ :=
  let G := fun a=>ofPredicate n L (tri a) hL (ht a)
  let B := (P.filter (fun p=>ordinaryDegree n L G p=1 ∧ coreDegree n L G p=5)).card
  let E := (P.filter (fun p=>ordinaryDegree n L G p=3)).card
  let Q := (P.filter (fun p=>ordinaryDegree n L G p=2 ∧ coreDegree n L G p=1)).card
  (3*(E : ℤ)+3*(Q : ℤ)-(B : ℤ)+1)/2

noncomputable def unrestrictedLowerOn {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (ht : ∀ a, TrianglePredicate n L (tri a)) (P : Finset Point) : ℤ :=
  max (UpperOpenMathClosedHalfCurvature.hybridGainLowerOn n L hL hn tri ht P)
    (sourceFreeLowerOn n L hL tri ht P)

noncomputable def escapeLowerOn {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (ht : ∀ a, TrianglePredicate n L (tri a)) (P : Finset Point) : ℤ :=
  let G := fun a=>ofPredicate n L (tri a) hL (ht a)
  let A := (P.filter (fun p=>ordinaryDegree n L G p=2 ∧ coreDegree n L G p=4 ∧ markedCount n L hL hn tri ht p=0)).card
  let B := (P.filter (fun p=>ordinaryDegree n L G p=1 ∧ coreDegree n L G p=5)).card
  1-(A : ℤ)-(((B+1)/2 : ℕ) : ℤ)

theorem unrestricted_score_simplifies {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (ht : ∀ a, TrianglePredicate n L (tri a)) (P : Finset Point) :
    unrestrictedLowerOn n L hL hn tri ht P=
      max (escapeLowerOn n L hL hn tri ht P) (sourceFreeLowerOn n L hL tri ht P) := by
  classical
  let G := fun a=>ofPredicate n L (tri a) hL (ht a)
  let A := (P.filter (fun p=>ordinaryDegree n L G p=2 ∧ coreDegree n L G p=4 ∧ markedCount n L hL hn tri ht p=0)).card
  let B := (P.filter (fun p=>ordinaryDegree n L G p=1 ∧ coreDegree n L G p=5)).card
  let E := (P.filter (fun p=>ordinaryDegree n L G p=3)).card
  let Q := (P.filter (fun p=>ordinaryDegree n L G p=2 ∧ coreDegree n L G p=1)).card
  change max (max (1-(A : ℤ)-(((B+1)/2 : ℕ) : ℤ))
      ((6*(E : ℤ)+5*(Q : ℤ)-2*(A : ℤ)-2*(B : ℤ)+3)/4))
      ((3*(E : ℤ)+3*(Q : ℤ)-(B : ℤ)+1)/2)=
    max (1-(A : ℤ)-(((B+1)/2 : ℕ) : ℤ)) ((3*(E : ℤ)+3*(Q : ℤ)-(B : ℤ)+1)/2)
  have gainLe : ((6*(E : ℤ)+5*(Q : ℤ)-2*(A : ℤ)-2*(B : ℤ)+3)/4)≤
      ((3*(E : ℤ)+3*(Q : ℤ)-(B : ℤ)+1)/2) := by omega
  rw [max_assoc,max_eq_right gainLe]

theorem unrestricted_dominates_half_gain {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (ht : ∀ a, TrianglePredicate n L (tri a)) (P : Finset Point) :
    UpperOpenMathClosedHalfCurvature.hybridGainLowerOn n L hL hn tri ht P≤
      unrestrictedLowerOn n L hL hn tri ht P := le_max_left _ _

theorem certificate_closed_unrestricted_lower_of_unique {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (triples : ∀ p∈core n L, (supports n L p).card=3)
    (unique : NoDoubleAntipodalRecipients n L hL hn tri ht)
    (P : Finset Point) (sub : P⊆core n L) (nonempty : P.Nonempty)
    (closed : SharedCoreClosed n L (fun a=>ofPredicate n L (tri a) hL (ht a)) P) :
    unrestrictedLowerOn n L hL hn tri ht P≤componentCost n L (fun a=>ofPredicate n L (tri a) hL (ht a)) P := by
  classical
  apply max_le
  · exact UpperOpenMathClosedHalfCurvature.certificate_closed_hybrid_gain_lower
      n L hL hn tri hi ht triples P sub nonempty closed
  · have gain := certificate_closed_no_source_gain_of_unique n L hL hn tri hi ht triples unique P sub closed
    dsimp only [sourceFreeLowerOn] at gain ⊢
    omega

theorem certificate_hybrid_no_source_component_defect_of_unique {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (triples : ∀ p∈core n L, (supports n L p).card=3)
    (unique : NoDoubleAntipodalRecipients n L hL hn tri ht) :
    let G := fun a=>ofPredicate n L (tri a) hL (ht a)
    (UpperEdgeInventory.edges n L\usedEdges G).card+
      (∑ s∈components n L G,unrestrictedLowerOn n L hL hn tri ht (componentVertices n L G s))≤
      (n : ℤ)*(n-2)-3*Fintype.card α := by
  classical
  let G := fun a=>ofPredicate n L (tri a) hL (ht a)
  have each (s : (coreGraph n L G).ConnectedComponent) (hs : s∈components n L G) :=
    certificate_closed_unrestricted_lower_of_unique n L hL hn tri hi ht triples unique (componentVertices n L G s)
      (component_subset n L G s) (component_nonempty n L G s) (component_closed n L hL tri ht s)
  have summed := sum_le_sum each
  have identity := certificate_component_cost_identity n L hL hn tri hi ht
  dsimp only at identity ⊢
  linarith

#print axioms degreeFrom_le_one_of_unique_neighbors
#print axioms certificate_no_source_correction_of_unique
#print axioms certificate_hybrid_no_source_component_defect_of_unique
#print axioms unrestricted_score_simplifies
end Kobon.UpperOpenMathN13Degree
