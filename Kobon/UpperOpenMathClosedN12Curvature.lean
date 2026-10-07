import Kobon.UpperOpenMathClosedHalfCurvature
import Kobon.UpperOpenMathN12Curvature

/-! Actual closed-component double-recipient charging and a componentwise
maximum with the existing strict/half-gain portfolio. -/
namespace Kobon.UpperOpenMathClosedN12Curvature
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

theorem certificate_closed_n12_recipient_gain {α : Type*} [Fintype α]
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
      3*((P.filter (fun p=>ordinaryDegree n L G p=2 ∧ coreDegree n L G p=1)).card : ℤ)-
      ((P.filter (fun p=>ordinaryDegree n L G p=1 ∧ coreDegree n L G p=2)).card : ℤ) := by
  classical
  let G := fun a => ofPredicate n L (tri a) hL (ht a)
  let a := ordinaryDegree n L G
  let d := coreDegree n L G
  let m := markedCount n L hL hn tri ht
  let A := P.filter (fun p => a p=2 ∧ d p=4 ∧ m p=0)
  let N := P.filter (fun p => a p+d p≠6)
  let B := P.filter (fun p => a p≤1 ∧ a p+d p≤2)
  let x := fun p => if a p+d p=6 then 0 else degreeFrom n L G A p
  have data := certificate_recipient_data n L hL hn tri hi ht triples
  have ha (p : Point) (hp : p∈P) : a p≤3 := data.ha p (sub hp)
  have had (p : Point) (hp : p∈P) : a p+d p≤6 := data.had p (sub hp)
  have hfive (p : Point) (hp : p∈P) : a p+d p≠5 := data.hfive p (sub hp)
  have hext (p : Point) (hp : p∈P) (ap : a p=3) : d p=3 ∧ m p=3 := data.hext p (sub hp) ap
  have hpartial (p : Point) (hp : p∈P) (ap : a p=2) (dp : d p=1) : 1≤m p := by
    have eq := marked_count_of_partial_triple n L hL hn tri hi ht p (sub hp) (triples p (sub hp)) ap dp
    change m p=1 at eq
    omega
  have hx (p : Point) (hp : p∈P) : x p≤d p := by
    dsimp [x]
    split_ifs
    · omega
    · exact degreeFrom_le n L G A p
  have hfull (p : Point) (hp : p∈P) (full : a p+d p=6) : x p=0 := by simp only [x,if_pos full]
  have aGlobal : A⊆unmarkedFullTwoCapSet n L hL hn tri ht := by
    intro p hp
    obtain ⟨hpP,ap,dp,mp⟩ := mem_filter.mp hp
    exact mem_filter.mpr ⟨sub hpP,ap,dp,mp⟩
  have hsmall (p : Point) (hp : p∈P) (small : a p+d p≤4) : x p≤2 := by
    have global := UpperOpenMathNonfullAntipodalRecipients.certificate_nonfull_anti_degree_le_two
      n L hL hn tri hi ht triples p (sub hp) small
    have mono := degreeFrom_mono n L G A (unmarkedFullTwoCapSet n L hL hn tri ht) aGlobal p
    change degreeFrom n L G (unmarkedFullTwoCapSet n L hL hn tri ht) p≤2 at global
    have lower : degreeFrom n L G A p≤2 := mono.trans global
    dsimp [x]
    split_ifs <;> omega
  have hbalanced (p : Point) (hp : p∈P) (ap : a p=2) (dp : d p=2) (mp : m p=0) : x p=0 := by
    have zero := certificate_balanced_anti_degree_zero n L hL hn tri hi ht triples p (sub hp) ap dp mp
    have mono := degreeFrom_mono n L G A (unmarkedFullTwoCapSet n L hL hn tri ht) aGlobal p
    change degreeFrom n L G (unmarkedFullTwoCapSet n L hL hn tri ht) p=0 at zero
    have localZero : degreeFrom n L G A p=0 := by omega
    dsimp [x]
    split_ifs <;> omega
  have aPoor : Disjoint A B := by
    apply disjoint_left.mpr
    intro p hpA hpB
    have two : a p=2 := (mem_filter.mp hpA).2.1
    have one := (mem_filter.mp hpB).2.1
    omega
  have unmarked (s : Point) (hs : s∈A) : m s=0 := (mem_filter.mp hs).2.2.2
  have cap := certificate_unmarked_cross_capacity n L hL hn tri hi ht triples P A sub (filter_subset _ _)
    closed unmarked aPoor
  have xPoor : (∑ p∈B,x p)=(UpperOpenMathUnmarkedCrossResources.crossEdges n L G A B).card := by
    calc
      _=∑ p∈B,degreeFrom n L G A p := by
        apply sum_congr rfl
        intro p hp
        have poor := (mem_filter.mp hp).2.2
        have noFull : ¬(a p+d p=6) := by omega
        exact if_neg noFull
      _=_ := degreeFrom_sum n L G A B aPoor
  have capacity : (∑ p∈P,m p)+(∑ p∈B,x p)≤∑ p∈B,d p := by
    change (∑ p∈P,m p)+(UpperOpenMathUnmarkedCrossResources.crossEdges n L G A B).card≤∑ p∈B,d p at cap
    rw [xPoor]
    exact cap
  have aNonfull : Disjoint A N := by
    apply disjoint_left.mpr
    intro p hpA hpN
    have two : a p=2 := (mem_filter.mp hpA).2.1
    have four : d p=4 := (mem_filter.mp hpA).2.2.1
    have noFull := (mem_filter.mp hpN).2
    omega
  have xsum : (∑ p∈P,x p)=∑ p∈N,degreeFrom n L G A p := by
    change (∑ p∈P,if a p+d p=6 then 0 else degreeFrom n L G A p)=
      ∑ p∈P.filter (fun p => a p+d p≠6),degreeFrom n L G A p
    rw [sum_filter]
    apply sum_congr rfl
    intro p hp
    by_cases full : a p+d p=6 <;> simp [full]
  have cone := UpperOpenMathClosedConeIncidence.certificate_closed_two_anti_cone n L hL hn tri hi ht triples P sub closed
  change 2*A.card≤(UpperOpenMathUnmarkedCrossResources.crossEdges n L G A N).card at cone
  have coneX : 2*A.card≤∑ p∈P,x p := by rw [xsum,degreeFrom_sum n L G A N aNonfull]; exact cone
  have hpartialZero (p : Point) (hp : p∈P) (ap : a p=2) (dp : d p=1) : x p=0 := by
    exact UpperOpenMathPartialRecipients.certificate_closed_partial_recipient_zero n L hL hn tri hi ht triples P sub p hp ap dp
  have hn12 (p : Point) (hp : p∈P) (ap : a p=1) (dp : d p=2) : x p≤1 := by
    have global := UpperOpenMathN12Recipient.certificate_n12_anti_degree_le_one n L hL hn tri hi ht triples p (sub hp) ap dp
    have mono := degreeFrom_mono n L G A (unmarkedFullTwoCapSet n L hL hn tri ht) aGlobal p
    change degreeFrom n L G (unmarkedFullTwoCapSet n L hL hn tri ht) p≤1 at global
    dsimp [x]
    split_ifs <;> omega
  have result := UpperOpenMathN12GainWeights.finite_n12_curvature_gain
    P a d m x ha had hfive hext hpartial hpartialZero hn12 hx hsmall hfull hbalanced capacity coneX
  have identity := UpperOpenMathTripleCurvature.closed_curvature_identity n L G P closed
    (fun p hp=>triples p (sub hp))
  change 0≤2*componentCost n L G P+
    ((P.filter (fun p=>a p=1 ∧ d p=5)).card : ℤ)+
    ((P.filter (fun p=>a p=1 ∧ d p=3 ∧ x p=2)).card : ℤ)-
    3*((P.filter (fun p=>a p=3)).card : ℤ)-
    3*((P.filter (fun p=>a p=2 ∧ d p=1)).card : ℤ)-
    ((P.filter (fun p=>a p=1 ∧ d p=2)).card : ℤ)
  change 0≤(∑ p∈P,(6-2*(a p : ℤ)-d p))+
    ((P.filter (fun p=>a p=1 ∧ d p=5)).card : ℤ)+
    ((P.filter (fun p=>a p=1 ∧ d p=3 ∧ x p=2)).card : ℤ)-
    3*((P.filter (fun p=>a p=3)).card : ℤ)-
    3*((P.filter (fun p=>a p=2 ∧ d p=1)).card : ℤ)-
    ((P.filter (fun p=>a p=1 ∧ d p=2)).card : ℤ) at result
  rw [←identity] at result
  exact result

noncomputable def n12RecipientLowerOn {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (ht : ∀ a, TrianglePredicate n L (tri a)) (P : Finset Point) : ℤ :=
  let G := fun a=>ofPredicate n L (tri a) hL (ht a)
  let B := (P.filter (fun p=>ordinaryDegree n L G p=1 ∧ coreDegree n L G p=5)).card
  let J := (P.filter (fun p=>ordinaryDegree n L G p=1 ∧ coreDegree n L G p=3 ∧
    closedRecipientCount n L hL hn tri ht P p=2)).card
  let E := (P.filter (fun p=>ordinaryDegree n L G p=3)).card
  let Q := (P.filter (fun p=>ordinaryDegree n L G p=2 ∧ coreDegree n L G p=1)).card
  let R := (P.filter (fun p=>ordinaryDegree n L G p=1 ∧ coreDegree n L G p=2)).card
  (3*(E : ℤ)+3*(Q : ℤ)+(R : ℤ)-(B : ℤ)-(J : ℤ)+1)/2

noncomputable def hybridN12LowerOn {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (ht : ∀ a, TrianglePredicate n L (tri a)) (P : Finset Point) : ℤ :=
  max (UpperOpenMathClosedHalfCurvature.hybridGainLowerOn n L hL hn tri ht P)
    (n12RecipientLowerOn n L hL hn tri ht P)

theorem certificate_closed_n12_lower {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (triples : ∀ p∈core n L, (supports n L p).card=3)
    (P : Finset Point) (sub : P⊆core n L)
    (closed : SharedCoreClosed n L (fun a=>ofPredicate n L (tri a) hL (ht a)) P) :
    n12RecipientLowerOn n L hL hn tri ht P≤
      componentCost n L (fun a=>ofPredicate n L (tri a) hL (ht a)) P := by
  have h := certificate_closed_n12_recipient_gain n L hL hn tri hi ht triples P sub closed
  dsimp only [n12RecipientLowerOn] at h ⊢
  omega

theorem certificate_closed_hybrid_n12_lower {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (triples : ∀ p∈core n L, (supports n L p).card=3)
    (P : Finset Point) (sub : P⊆core n L) (nonempty : P.Nonempty)
    (closed : SharedCoreClosed n L (fun a=>ofPredicate n L (tri a) hL (ht a)) P) :
    hybridN12LowerOn n L hL hn tri ht P≤
      componentCost n L (fun a=>ofPredicate n L (tri a) hL (ht a)) P := by
  apply max_le
  · exact UpperOpenMathClosedHalfCurvature.certificate_closed_hybrid_gain_lower
      n L hL hn tri hi ht triples P sub nonempty closed
  · exact certificate_closed_n12_lower n L hL hn tri hi ht triples P sub closed

theorem certificate_hybrid_n12_component_defect {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (triples : ∀ p∈core n L, (supports n L p).card=3) :
    let G := fun a=>ofPredicate n L (tri a) hL (ht a)
    (UpperEdgeInventory.edges n L\usedEdges G).card+
      (∑ s∈components n L G,hybridN12LowerOn n L hL hn tri ht (componentVertices n L G s))≤
      (n : ℤ)*(n-2)-3*Fintype.card α := by
  classical
  let G := fun a=>ofPredicate n L (tri a) hL (ht a)
  have each (s : (coreGraph n L G).ConnectedComponent) (hs : s∈components n L G) :=
    certificate_closed_hybrid_n12_lower n L hL hn tri hi ht triples (componentVertices n L G s)
      (component_subset n L G s) (component_nonempty n L G s) (component_closed n L hL tri ht s)
  have summed := sum_le_sum each
  have identity := certificate_component_cost_identity n L hL hn tri hi ht
  dsimp only at identity ⊢
  linarith

theorem hybrid_n12_dominates {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (ht : ∀ a, TrianglePredicate n L (tri a)) (P : Finset Point) :
    UpperOpenMathClosedHalfCurvature.hybridGainLowerOn n L hL hn tri ht P≤
      hybridN12LowerOn n L hL hn tri ht P := le_max_left _ _

theorem certificate_closed_n12_source_free_gain {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (triples : ∀ p∈core n L, (supports n L p).card=3)
    (P : Finset Point) (sub : P⊆core n L)
    (closed : SharedCoreClosed n L (fun a=>ofPredicate n L (tri a) hL (ht a)) P) :
    let G := fun a=>ofPredicate n L (tri a) hL (ht a)
    0≤2*componentCost n L G P+
      ((P.filter (fun p=>ordinaryDegree n L G p=1 ∧ coreDegree n L G p=5)).card : ℤ)-
      3*((P.filter (fun p=>ordinaryDegree n L G p=3)).card : ℤ)-
      3*((P.filter (fun p=>ordinaryDegree n L G p=2 ∧ coreDegree n L G p=1)).card : ℤ)-
      ((P.filter (fun p=>ordinaryDegree n L G p=1 ∧ coreDegree n L G p=2)).card : ℤ) := by
  classical
  let G := fun a=>ofPredicate n L (tri a) hL (ht a)
  have empty : P.filter (fun p=>ordinaryDegree n L G p=1 ∧ coreDegree n L G p=3 ∧
      closedRecipientCount n L hL hn tri ht P p=2)=∅ :=
    UpperOpenMathN13Degree.certificate_closed_recipient_correction_empty_of_unique n L hL hn tri ht
      (UpperOpenMathN13Curvature.certificate_no_double_recipients n L hL hn tri hi ht triples) P sub
  have result := certificate_closed_n12_recipient_gain n L hL hn tri hi ht triples P sub closed
  dsimp only at result ⊢
  rw [empty,card_empty,Nat.cast_zero,add_zero] at result
  exact result

noncomputable def sourceFreeN12LowerOn {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L)
    (tri : α → Triple) (ht : ∀ a, TrianglePredicate n L (tri a)) (P : Finset Point) : ℤ :=
  let G := fun a=>ofPredicate n L (tri a) hL (ht a)
  let B := (P.filter (fun p=>ordinaryDegree n L G p=1 ∧ coreDegree n L G p=5)).card
  let E := (P.filter (fun p=>ordinaryDegree n L G p=3)).card
  let Q := (P.filter (fun p=>ordinaryDegree n L G p=2 ∧ coreDegree n L G p=1)).card
  let R := (P.filter (fun p=>ordinaryDegree n L G p=1 ∧ coreDegree n L G p=2)).card
  (3*(E : ℤ)+3*(Q : ℤ)+(R : ℤ)-(B : ℤ)+1)/2

noncomputable def sourceFreeN12HybridOn {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (ht : ∀ a, TrianglePredicate n L (tri a)) (P : Finset Point) : ℤ :=
  max (UpperOpenMathN13Degree.escapeLowerOn n L hL hn tri ht P)
    (sourceFreeN12LowerOn n L hL tri ht P)

theorem certificate_closed_n12_hybrid_lower {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (triples : ∀ p∈core n L, (supports n L p).card=3)
    (P : Finset Point) (sub : P⊆core n L) (nonempty : P.Nonempty)
    (closed : SharedCoreClosed n L (fun a=>ofPredicate n L (tri a) hL (ht a)) P) :
    sourceFreeN12HybridOn n L hL hn tri ht P≤componentCost n L (fun a=>ofPredicate n L (tri a) hL (ht a)) P := by
  classical
  let G := fun a=>ofPredicate n L (tri a) hL (ht a)
  let A := (P.filter (fun p=>ordinaryDegree n L G p=2 ∧ coreDegree n L G p=4 ∧ markedCount n L hL hn tri ht p=0)).card
  let B := (P.filter (fun p=>ordinaryDegree n L G p=1 ∧ coreDegree n L G p=5)).card
  let E := (P.filter (fun p=>ordinaryDegree n L G p=3)).card
  let Q := (P.filter (fun p=>ordinaryDegree n L G p=2 ∧ coreDegree n L G p=1)).card
  let R := (P.filter (fun p=>ordinaryDegree n L G p=1 ∧ coreDegree n L G p=2)).card
  have old := UpperOpenMathPaidCurvatureBound.certificate_closed_half_penalty_bound n L hL hn tri hi ht triples P sub nonempty closed
  have gain := certificate_closed_n12_source_free_gain n L hL hn tri hi ht triples P sub closed
  change 1≤componentCost n L G P+((A : ℤ)+(((B+1)/2 : ℕ) : ℤ)) at old
  change 0≤2*componentCost n L G P+(B : ℤ)-3*(E : ℤ)-3*(Q : ℤ)-(R : ℤ) at gain
  change max (1-(A : ℤ)-(((B+1)/2 : ℕ) : ℤ))
    ((3*(E : ℤ)+3*(Q : ℤ)+(R : ℤ)-(B : ℤ)+1)/2)≤componentCost n L G P
  apply max_le <;> omega

theorem certificate_n12_source_free_hybrid_component_defect {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (triples : ∀ p∈core n L, (supports n L p).card=3) :
    let G := fun a=>ofPredicate n L (tri a) hL (ht a)
    (UpperEdgeInventory.edges n L\usedEdges G).card+
      (∑ s∈components n L G,sourceFreeN12HybridOn n L hL hn tri ht (componentVertices n L G s))≤
      (n : ℤ)*(n-2)-3*Fintype.card α := by
  classical
  let G := fun a=>ofPredicate n L (tri a) hL (ht a)
  have each (s : (coreGraph n L G).ConnectedComponent) (hs : s∈components n L G) :=
    certificate_closed_n12_hybrid_lower n L hL hn tri hi ht triples (componentVertices n L G s)
      (component_subset n L G s) (component_nonempty n L G s) (component_closed n L hL tri ht s)
  have summed := sum_le_sum each
  have identity := certificate_component_cost_identity n L hL hn tri hi ht
  dsimp only at identity ⊢
  linarith

#print axioms certificate_closed_n12_recipient_gain
#print axioms certificate_hybrid_n12_component_defect
#print axioms certificate_closed_n12_source_free_gain
#print axioms certificate_n12_source_free_hybrid_component_defect

theorem source_free_n12_dominates {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (ht : ∀ a, TrianglePredicate n L (tri a)) (P : Finset Point) :
    UpperOpenMathN13Degree.unrestrictedLowerOn n L hL hn tri ht P≤
      sourceFreeN12HybridOn n L hL hn tri ht P := by
  classical
  rw [UpperOpenMathN13Degree.unrestricted_score_simplifies]
  apply max_le_max le_rfl
  dsimp only [UpperOpenMathN13Degree.sourceFreeLowerOn,sourceFreeN12LowerOn]
  omega

#print axioms source_free_n12_dominates
end Kobon.UpperOpenMathClosedN12Curvature
