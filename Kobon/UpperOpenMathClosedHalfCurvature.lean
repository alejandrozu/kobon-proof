import Kobon.UpperOpenMathClosedConeIncidence
import Kobon.UpperOpenMathTwoThirdCurvature
import Kobon.UpperOpenMathHalfCurvatureWeights
import Kobon.UpperOpenMathHalfCurvatureGainWeights
import Kobon.UpperOpenMathOneCapThreeCoreDegree
import Kobon.UpperOpenMathPaidCurvatureBound

/-! Componentwise half-curvature and the strongest of the verified local
rounded corrections. -/
namespace Kobon.UpperOpenMathClosedHalfCurvature
open Cells FanGeometry UpperVertexBudget UpperTriangleIncidence UpperSharedIncidence
  UpperCoreExtraction UpperOpenMathCapHeavyTriples UpperOpenMathCoreComponents
  UpperOpenMathMarkedPorts UpperOpenMathUnmarkedCrossResources
  UpperOpenMathAntipodalAdjacency UpperOpenMathTwoThirdCurvature Finset
open scoped BigOperators
set_option maxHeartbeats 1000000

theorem certificate_closed_half_gain {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (triples : ∀ p∈core n L, (supports n L p).card=3)
    (P : Finset Point) (sub : P⊆core n L)
    (closed : SharedCoreClosed n L (fun a => ofPredicate n L (tri a) hL (ht a)) P) :
    let G := fun a => ofPredicate n L (tri a) hL (ht a)
    0≤4*componentCost n L G P+
      2*((P.filter (fun p => ordinaryDegree n L G p=2 ∧ coreDegree n L G p=4 ∧ markedCount n L hL hn tri ht p=0)).card : ℤ)+
      2*((P.filter (fun p => ordinaryDegree n L G p=1 ∧ coreDegree n L G p=5)).card : ℤ)-
      6*((P.filter (fun p => ordinaryDegree n L G p=3)).card : ℤ)-
      5*((P.filter (fun p => ordinaryDegree n L G p=2 ∧ coreDegree n L G p=1)).card : ℤ) := by
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
  have hbalanced (p : Point) (hp : p∈P) (ap : a p=2) (dp : d p=2) (mp : m p=0) : x p=0 := by
    have zero := certificate_balanced_anti_degree_zero n L hL hn tri hi ht triples p (sub hp) ap dp mp
    have mono := degreeFrom_mono n L G A (unmarkedFullTwoCapSet n L hL hn tri ht) aGlobal p
    change degreeFrom n L G (unmarkedFullTwoCapSet n L hL hn tri ht) p=0 at zero
    have localZero : degreeFrom n L G A p=0 := by omega
    dsimp [x]
    split_ifs <;> omega
  have narrow (p : Point) (hp : p∈P) (ap : a p=1) (dp : d p=3) : x p≤2 := by
    have global := UpperOpenMathOneCapThreeCoreDegree.certificate_n13_anti_degree_le_two
      n L hL hn tri hi ht triples p (sub hp) ap dp
    have mono := degreeFrom_mono n L G A (unmarkedFullTwoCapSet n L hL hn tri ht) aGlobal p
    change degreeFrom n L G (unmarkedFullTwoCapSet n L hL hn tri ht) p≤2 at global
    have lower : degreeFrom n L G A p≤2 := mono.trans global
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
  have result := UpperOpenMathHalfCurvatureGainWeights.finite_half_curvature_gain P a d m x ha had hfive hext hpartial
    hx hfull hbalanced capacity coneX
  have jEmpty : P.filter (fun p => a p=1 ∧ d p=3 ∧ x p=3)=∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro p hp
    obtain ⟨hpP,ap,dp,xp⟩ := mem_filter.mp hp
    have bound := narrow p hpP ap dp
    omega
  rw [jEmpty,card_empty,Nat.cast_zero,add_zero] at result
  have identity := UpperOpenMathTripleCurvature.closed_curvature_identity n L G P closed (fun p hp => triples p (sub hp))
  change 0≤4*componentCost n L G P+2*(A.card : ℤ)+2*(P.filter (fun p => a p=1 ∧ d p=5)).card-
    6*(P.filter (fun p => a p=3)).card-5*(P.filter (fun p => a p=2 ∧ d p=1)).card
  change 0≤2*(∑ p∈P,(6-2*(a p : ℤ)-d p))+2*(A.card : ℤ)+
    2*(P.filter (fun p => a p=1 ∧ d p=5)).card-
    6*(P.filter (fun p => a p=3)).card-5*(P.filter (fun p => a p=2 ∧ d p=1)).card at result
  rw [← identity] at result
  linarith

theorem certificate_closed_half_cost {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (triples : ∀ p∈core n L, (supports n L p).card=3)
    (P : Finset Point) (sub : P⊆core n L)
    (closed : SharedCoreClosed n L (fun a => ofPredicate n L (tri a) hL (ht a)) P) :
    let G := fun a => ofPredicate n L (tri a) hL (ht a)
    0≤2*componentCost n L G P+
      ((P.filter (fun p => ordinaryDegree n L G p=2 ∧ coreDegree n L G p=4 ∧ markedCount n L hL hn tri ht p=0)).card : ℤ)+
      ((P.filter (fun p => ordinaryDegree n L G p=1 ∧ coreDegree n L G p=5)).card : ℤ) := by
  have gain := certificate_closed_half_gain n L hL hn tri hi ht triples P sub closed
  dsimp only at gain ⊢
  have posE : (0 : ℤ)≤((P.filter (fun p => ordinaryDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) p=3)).card : ℤ) := by positivity
  have posP : (0 : ℤ)≤((P.filter (fun p => ordinaryDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) p=2 ∧
    coreDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) p=1)).card : ℤ) := by positivity
  linarith

noncomputable def hybridLowerOn {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (ht : ∀ a, TrianglePredicate n L (tri a)) (P : Finset Point) : ℤ :=
  let G := fun a => ofPredicate n L (tri a) hL (ht a)
  let A := (P.filter (fun p => ordinaryDegree n L G p=2 ∧ coreDegree n L G p=4 ∧ markedCount n L hL hn tri ht p=0)).card
  let B := (P.filter (fun p => ordinaryDegree n L G p=1 ∧ coreDegree n L G p=5)).card
  max (1-(A : ℤ)-(((B+1)/2 : ℕ) : ℤ)) (-(((A+B)/2 : ℕ) : ℤ))

theorem certificate_closed_hybrid_lower {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (triples : ∀ p∈core n L, (supports n L p).card=3)
    (P : Finset Point) (sub : P⊆core n L) (nonempty : P.Nonempty)
    (closed : SharedCoreClosed n L (fun a => ofPredicate n L (tri a) hL (ht a)) P) :
    hybridLowerOn n L hL hn tri ht P≤componentCost n L (fun a => ofPredicate n L (tri a) hL (ht a)) P := by
  classical
  let G := fun a => ofPredicate n L (tri a) hL (ht a)
  let A := (P.filter (fun p => ordinaryDegree n L G p=2 ∧ coreDegree n L G p=4 ∧ markedCount n L hL hn tri ht p=0)).card
  let B := (P.filter (fun p => ordinaryDegree n L G p=1 ∧ coreDegree n L G p=5)).card
  have old := UpperOpenMathPaidCurvatureBound.certificate_closed_half_penalty_bound n L hL hn tri hi ht triples P sub nonempty closed
  have new := certificate_closed_half_cost n L hL hn tri hi ht triples P sub closed
  change 1≤componentCost n L G P+((A : ℤ)+(((B+1)/2 : ℕ) : ℤ)) at old
  change 0≤2*componentCost n L G P+(A : ℤ)+(B : ℤ) at new
  change max (1-(A : ℤ)-(((B+1)/2 : ℕ) : ℤ)) (-(((A+B)/2 : ℕ) : ℤ))≤componentCost n L G P
  apply max_le
  · omega
  · omega

theorem certificate_hybrid_component_defect {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (triples : ∀ p∈core n L, (supports n L p).card=3) :
    let G := fun a => ofPredicate n L (tri a) hL (ht a)
    (UpperEdgeInventory.edges n L\usedEdges G).card+
      (∑ s∈components n L G,hybridLowerOn n L hL hn tri ht (componentVertices n L G s))≤
      (n : ℤ)*(n-2)-3*Fintype.card α := by
  classical
  let G := fun a => ofPredicate n L (tri a) hL (ht a)
  have each (s : (coreGraph n L G).ConnectedComponent) (hs : s∈components n L G) :=
    certificate_closed_hybrid_lower n L hL hn tri hi ht triples (componentVertices n L G s)
      (component_subset n L G s) (component_nonempty n L G s) (component_closed n L hL tri ht s)
  have summed := sum_le_sum each
  have identity := certificate_component_cost_identity n L hL hn tri hi ht
  dsimp only at identity ⊢
  linarith

#print axioms certificate_closed_half_cost
#print axioms certificate_closed_half_gain
#print axioms certificate_hybrid_component_defect

noncomputable def hybridGainLowerOn {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (ht : ∀ a, TrianglePredicate n L (tri a)) (P : Finset Point) : ℤ :=
  let G := fun a => ofPredicate n L (tri a) hL (ht a)
  let A := (P.filter (fun p => ordinaryDegree n L G p=2 ∧ coreDegree n L G p=4 ∧ markedCount n L hL hn tri ht p=0)).card
  let B := (P.filter (fun p => ordinaryDegree n L G p=1 ∧ coreDegree n L G p=5)).card
  let E := (P.filter (fun p => ordinaryDegree n L G p=3)).card
  let Q := (P.filter (fun p => ordinaryDegree n L G p=2 ∧ coreDegree n L G p=1)).card
  max (1-(A : ℤ)-(((B+1)/2 : ℕ) : ℤ))
    ((6*(E : ℤ)+5*(Q : ℤ)-2*(A : ℤ)-2*(B : ℤ)+3)/4)

theorem certificate_closed_hybrid_gain_lower {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (triples : ∀ p∈core n L, (supports n L p).card=3)
    (P : Finset Point) (sub : P⊆core n L) (nonempty : P.Nonempty)
    (closed : SharedCoreClosed n L (fun a => ofPredicate n L (tri a) hL (ht a)) P) :
    hybridGainLowerOn n L hL hn tri ht P≤componentCost n L (fun a => ofPredicate n L (tri a) hL (ht a)) P := by
  classical
  let G := fun a => ofPredicate n L (tri a) hL (ht a)
  let A := (P.filter (fun p => ordinaryDegree n L G p=2 ∧ coreDegree n L G p=4 ∧ markedCount n L hL hn tri ht p=0)).card
  let B := (P.filter (fun p => ordinaryDegree n L G p=1 ∧ coreDegree n L G p=5)).card
  let E := (P.filter (fun p => ordinaryDegree n L G p=3)).card
  let Q := (P.filter (fun p => ordinaryDegree n L G p=2 ∧ coreDegree n L G p=1)).card
  have old := UpperOpenMathPaidCurvatureBound.certificate_closed_half_penalty_bound n L hL hn tri hi ht triples P sub nonempty closed
  have gain := certificate_closed_half_gain n L hL hn tri hi ht triples P sub closed
  change 1≤componentCost n L G P+((A : ℤ)+(((B+1)/2 : ℕ) : ℤ)) at old
  change 0≤4*componentCost n L G P+2*(A : ℤ)+2*(B : ℤ)-6*(E : ℤ)-5*(Q : ℤ) at gain
  change max (1-(A : ℤ)-(((B+1)/2 : ℕ) : ℤ))
    ((6*(E : ℤ)+5*(Q : ℤ)-2*(A : ℤ)-2*(B : ℤ)+3)/4)≤componentCost n L G P
  apply max_le
  · omega
  · omega

theorem certificate_hybrid_gain_component_defect {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (triples : ∀ p∈core n L, (supports n L p).card=3) :
    let G := fun a => ofPredicate n L (tri a) hL (ht a)
    (UpperEdgeInventory.edges n L\usedEdges G).card+
      (∑ s∈components n L G,hybridGainLowerOn n L hL hn tri ht (componentVertices n L G s))≤
      (n : ℤ)*(n-2)-3*Fintype.card α := by
  classical
  let G := fun a => ofPredicate n L (tri a) hL (ht a)
  have each (s : (coreGraph n L G).ConnectedComponent) (hs : s∈components n L G) :=
    certificate_closed_hybrid_gain_lower n L hL hn tri hi ht triples (componentVertices n L G s)
      (component_subset n L G s) (component_nonempty n L G s) (component_closed n L hL tri ht s)
  have summed := sum_le_sum each
  have identity := certificate_component_cost_identity n L hL hn tri hi ht
  dsimp only at identity ⊢
  linarith

theorem hybrid_gain_dominates {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (ht : ∀ a, TrianglePredicate n L (tri a)) (P : Finset Point) :
    hybridLowerOn n L hL hn tri ht P≤hybridGainLowerOn n L hL hn tri ht P := by
  classical
  let G := fun a => ofPredicate n L (tri a) hL (ht a)
  let A := (P.filter (fun p => ordinaryDegree n L G p=2 ∧ coreDegree n L G p=4 ∧ markedCount n L hL hn tri ht p=0)).card
  let B := (P.filter (fun p => ordinaryDegree n L G p=1 ∧ coreDegree n L G p=5)).card
  let E := (P.filter (fun p => ordinaryDegree n L G p=3)).card
  let Q := (P.filter (fun p => ordinaryDegree n L G p=2 ∧ coreDegree n L G p=1)).card
  change max (1-(A : ℤ)-(((B+1)/2 : ℕ) : ℤ)) (-(((A+B)/2 : ℕ) : ℤ))≤
    max (1-(A : ℤ)-(((B+1)/2 : ℕ) : ℤ)) ((6*(E : ℤ)+5*(Q : ℤ)-2*(A : ℤ)-2*(B : ℤ)+3)/4)
  apply max_le_max le_rfl
  omega

#print axioms certificate_hybrid_gain_component_defect
#print axioms hybrid_gain_dominates
end Kobon.UpperOpenMathClosedHalfCurvature
