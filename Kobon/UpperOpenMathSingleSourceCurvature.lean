import Kobon.UpperOpenMathClosedHalfCurvature
import Kobon.UpperOpenMathSingleSourceWeights
/-! An actual closed all-triple component with at most one antipodal full
two-cap source has no negative correction for that source. Its recipient
capacity is derived from the finite source set, not assumed. -/
namespace Kobon.UpperOpenMathSingleSourceCurvature
open Cells FanGeometry UpperVertexBudget UpperTriangleIncidence UpperSharedIncidence
  UpperCoreExtraction UpperOpenMathCapHeavyTriples UpperOpenMathCoreComponents
  UpperOpenMathMarkedPorts UpperOpenMathUnmarkedCrossResources
  UpperOpenMathAntipodalAdjacency UpperOpenMathTwoThirdCurvature Finset
open scoped BigOperators
set_option maxHeartbeats 1000000

theorem certificate_closed_single_source_gain {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (triples : ∀ p∈core n L, (supports n L p).card=3)
    (P : Finset Point) (sub : P⊆core n L)
    (closed : SharedCoreClosed n L (fun a => ofPredicate n L (tri a) hL (ht a)) P)
    (small : (P.filter (fun p => ordinaryDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) p=2 ∧
      coreDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) p=4 ∧ markedCount n L hL hn tri ht p=0)).card≤1) :
    let G := fun a => ofPredicate n L (tri a) hL (ht a)
    0≤2*componentCost n L G P+
      ((P.filter (fun p => ordinaryDegree n L G p=1 ∧ coreDegree n L G p=5)).card : ℤ)-
      3*((P.filter (fun p => ordinaryDegree n L G p=3)).card : ℤ)-
      2*((P.filter (fun p => ordinaryDegree n L G p=2 ∧ coreDegree n L G p=1)).card : ℤ) := by
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
  have smallA : A.card≤1 := small
  have hsmall (p : Point) (hp : p∈P) : x p≤1 := by
    dsimp [x]
    split_ifs with full
    · omega
    · have pnot : p∉A := by
        intro h
        have ap : a p=2 := (mem_filter.mp h).2.1
        have dp : d p=4 := (mem_filter.mp h).2.2.1
        omega
      change ((twoCoreEdges n L G).filter (fun e => p∈e ∧ (e∩A).Nonempty)).card≤1
      apply card_le_one.mpr
      intro e he f hf
      obtain ⟨he,hpe,s,hs⟩ := mem_filter.mp he
      obtain ⟨hf,hpf,t,ht⟩ := mem_filter.mp hf
      obtain ⟨hse,hsA⟩ := mem_inter.mp hs
      obtain ⟨htf,htA⟩ := mem_inter.mp ht
      have same : s=t := (card_le_one.mp smallA) s hsA t htA
      have pair (e : Edge) (he : e∈twoCoreEdges n L G) (hpe : p∈e)
          (s : Point) (hsA : s∈A) (hse : s∈e) : e={p,s} := by
        have ne : p≠s := fun hh => pnot (hh.symm ▸ hsA)
        apply Eq.symm
        apply eq_of_subset_of_card_le
        · intro q hq
          rcases mem_insert.mp hq with hq|hq
          · simpa only [hq] using hpe
          · simpa only [mem_singleton.mp hq] using hse
        · rw [card_pair ne,used_edge_card G (mem_filter.mp (mem_sdiff.mp he).1).1]
      rw [pair e he hpe s hsA hse,pair f hf hpf t htA htf,same]
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
  have result := UpperOpenMathSingleSourceWeights.finite_single_source_curvature_gain P a d m x ha had hfive hext hpartial
    hx hsmall hfull hbalanced capacity coneX
  have identity := UpperOpenMathTripleCurvature.closed_curvature_identity n L G P closed (fun p hp => triples p (sub hp))
  change 0≤2*componentCost n L G P+(P.filter (fun p => a p=1 ∧ d p=5)).card-
    3*(P.filter (fun p => a p=3)).card-2*(P.filter (fun p => a p=2 ∧ d p=1)).card
  change 0≤(∑ p∈P,(6-2*(a p : ℤ)-d p))+(P.filter (fun p => a p=1 ∧ d p=5)).card-
    3*(P.filter (fun p => a p=3)).card-2*(P.filter (fun p => a p=2 ∧ d p=1)).card at result
  rw [← identity] at result
  linarith

#print axioms certificate_closed_single_source_gain
end Kobon.UpperOpenMathSingleSourceCurvature



