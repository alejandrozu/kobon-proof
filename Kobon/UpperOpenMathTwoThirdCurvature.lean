import Kobon.UpperOpenMathUnmarkedCrossResources
import Kobon.UpperOpenMathTwoThirdCurvatureWeights
import Kobon.UpperOpenMathAntipodalConeIncidence
import Kobon.UpperOpenMathAntipodalBalancedAdjacency

/-! Actual unrestricted triple curvature with a two-thirds coefficient on
the residual unmarked full two-cap correction. -/
namespace Kobon.UpperOpenMathTwoThirdCurvature
open Cells FanGeometry UpperVertexBudget UpperTriangleIncidence UpperSharedIncidence
  UpperCoreExtraction UpperOpenMathCapHeavyTriples UpperOpenMathCoreComponents
  UpperOpenMathMarkedPorts UpperOpenMathUnmarkedCrossResources
  UpperOpenMathAntipodalAdjacency UpperOpenMathAntipodalFullNeighborPair Finset
open scoped BigOperators
set_option maxHeartbeats 1000000

theorem certificate_balanced_anti_degree_zero {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (triples : ∀ p∈core n L, (supports n L p).card=3)
    (p : Point) (hp : p∈core n L)
    (ap : ordinaryDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) p=2)
    (dp : coreDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) p=2)
    (mp : markedCount n L hL hn tri ht p=0) :
    degreeFrom n L (fun a => ofPredicate n L (tri a) hL (ht a))
      (unmarkedFullTwoCapSet n L hL hn tri ht) p=0 := by
  classical
  let G := fun a => ofPredicate n L (tri a) hL (ht a)
  let A := unmarkedFullTwoCapSet n L hL hn tri ht
  unfold degreeFrom
  apply card_eq_zero.mpr
  apply eq_empty_iff_forall_notMem.mpr
  intro e he
  obtain ⟨he,hpe,s,hs⟩ := mem_filter.mp he
  obtain ⟨hse,hsA⟩ := mem_inter.mp hs
  obtain ⟨hsCore,as2,ds4,ms0⟩ := mem_filter.mp hsA
  have ne : s≠p := by
    intro h
    have ds : coreDegree n L G s=4 := ds4
    have dpp : coreDegree n L G p=2 := dp
    rw [h] at ds
    omega
  have pair : e={s,p} := by
    apply Eq.symm
    apply eq_of_subset_of_card_le
    · intro q hq
      rcases mem_insert.mp hq with hq|hq
      · simpa only [hq] using hse
      · simpa only [mem_singleton.mp hq] using hpe
    · rw [card_pair ne,used_edge_card G (mem_filter.mp (mem_sdiff.mp he).1).1]
  exact UpperOpenMathAntipodalBalancedAdjacency.certificate_unmarked_full_balanced_not_adjacent
    n L hL hn tri hi ht triples s p hsCore hp as2 ap ds4 dp ms0 mp (by simpa only [pair] using he)

noncomputable def recipientCount {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (ht : ∀ a, TrianglePredicate n L (tri a)) (p : Point) : ℕ :=
  let G := fun a => ofPredicate n L (tri a) hL (ht a)
  if ordinaryDegree n L G p+coreDegree n L G p=6 then 0 else
    degreeFrom n L G (unmarkedFullTwoCapSet n L hL hn tri ht) p

structure RecipientData {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (ht : ∀ a, TrianglePredicate n L (tri a)) : Prop where
  ha : ∀ p∈core n L, ordinaryDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) p≤3
  had : ∀ p∈core n L, ordinaryDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) p+
    coreDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) p≤6
  hfive : ∀ p∈core n L, ordinaryDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) p+
    coreDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) p≠5
  hext : ∀ p∈core n L, ordinaryDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) p=3 →
    coreDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) p=3 ∧ markedCount n L hL hn tri ht p=3
  hx : ∀ p∈core n L, recipientCount n L hL hn tri ht p≤coreDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) p
  hfull : ∀ p∈core n L, ordinaryDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) p+
    coreDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) p=6 → recipientCount n L hL hn tri ht p=0
  hbalanced : ∀ p∈core n L, ordinaryDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) p=2 →
    coreDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) p=2 → markedCount n L hL hn tri ht p=0 →
    recipientCount n L hL hn tri ht p=0
  capacity : (∑ p∈core n L, markedCount n L hL hn tri ht p)+
    (∑ p∈(core n L).filter (fun p => ordinaryDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) p≤1 ∧
      ordinaryDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) p+
        coreDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) p≤2), recipientCount n L hL hn tri ht p)≤
    ∑ p∈(core n L).filter (fun p => ordinaryDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) p≤1 ∧
      ordinaryDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) p+
        coreDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) p≤2),
      coreDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) p
  cone : 2*(unmarkedFullTwoCapSet n L hL hn tri ht).card≤∑ p∈core n L,recipientCount n L hL hn tri ht p

theorem certificate_recipient_data {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (triples : ∀ p∈core n L, (supports n L p).card=3) : RecipientData n L hL hn tri ht := by
  classical
  let G := fun a => ofPredicate n L (tri a) hL (ht a)
  let P := core n L
  let a := ordinaryDegree n L G
  let d := coreDegree n L G
  let m := markedCount n L hL hn tri ht
  let A := unmarkedFullTwoCapSet n L hL hn tri ht
  let N := UpperOpenMathAntipodalConeIncidence.nonfullCoreSet n L G
  let B := P.filter (fun p => a p≤1 ∧ a p+d p≤2)
  let x := fun p => if a p+d p=6 then 0 else degreeFrom n L G A p
  have ha (p : Point) (hp : p∈P) : a p≤3 := by
    have hh := UpperOpenMathActualFans.certificate_local_fan_bound n L hL hn tri hi ht p hp
    rw [triples p hp] at hh
    exact hh
  have had (p : Point) (hp : p∈P) : a p+d p≤6 := by
    have hh := UpperOpenMathMixedCapBudget.certificate_local_combined_degree n L hL hn tri hi ht p hp
    rw [triples p hp] at hh
    exact hh
  have hfive (p : Point) (hp : p∈P) : a p+d p≠5 :=
    UpperOpenMathTripleDegreeThree.certificate_triple_not_five n L hL hn tri hi ht p hp (triples p hp)
  have hext (p : Point) (hp : p∈P) (hpA : a p=3) : d p=3 ∧ m p=3 := by
    refine ⟨?_,marked_count_of_extremal_triple n L hL hn tri hi ht p hp (triples p hp) hpA⟩
    have he : 2*(supports n L p).card-3≤ordinaryDegree n L G p := by
      change 2*(supports n L p).card-3≤a p
      rw [triples p hp,hpA]
    exact UpperOpenMathSupportedCores.certificate_extremal_neighbor_count n L hL hn tri hi ht p hp he
  have hx (p : Point) (hp : p∈P) : x p≤d p := by
    dsimp [x]
    split_ifs
    · omega
    · exact degreeFrom_le n L G A p
  have hfull (p : Point) (hp : p∈P) (full : a p+d p=6) : x p=0 := by simp only [x,if_pos full]
  have hbalanced (p : Point) (hp : p∈P) (ap : a p=2) (dp : d p=2) (mp : m p=0) : x p=0 := by
    have zero := certificate_balanced_anti_degree_zero n L hL hn tri hi ht triples p hp ap dp mp
    change degreeFrom n L G A p=0 at zero
    dsimp [x]
    split_ifs <;> omega
  have aSub : A⊆P := filter_subset _ _
  have aPoor : Disjoint A B := by
    apply disjoint_left.mpr
    intro p hpA hpB
    have two : a p=2 := (mem_filter.mp hpA).2.1
    have one := (mem_filter.mp hpB).2.1
    omega
  have unmarked (s : Point) (hs : s∈A) : m s=0 := (mem_filter.mp hs).2.2.2
  have closed : SharedCoreClosed n L G P := by
    intro e he p hpe hp
    exact (mem_powersetCard.mp (UpperCoreCombinatorics.core_edge_subset n L hL tri ht he)).1
  have cap := certificate_unmarked_cross_capacity n L hL hn tri hi ht triples P A (by rfl) aSub closed unmarked aPoor
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
    obtain ⟨_,ap,dp,mp⟩ := mem_filter.mp hpA
    change a p=2 at ap
    change d p=4 at dp
    have nonfull := (mem_filter.mp hpN).2
    apply nonfull
    change a p+d p=6
    omega
  have xsum : (∑ p∈P,x p)=∑ p∈N,degreeFrom n L G A p := by
    have nEq : N=P.filter (fun p => a p+d p≠6) := by
      ext p
      simp only [N,UpperOpenMathAntipodalConeIncidence.nonfullCoreSet,mem_filter,FullAt]
      rfl
    rw [nEq]
    change (∑ p∈P,if a p+d p=6 then 0 else degreeFrom n L G A p)=
      ∑ p∈P.filter (fun p => ¬(a p+d p=6)),degreeFrom n L G A p
    rw [sum_filter]
    apply sum_congr rfl
    intro p hp
    by_cases full : a p+d p=6 <;> simp [full]
  have cone := UpperOpenMathAntipodalConeIncidence.certificate_two_anti_le_nonfull_cross_edges n L hL hn tri hi ht triples
  change 2*A.card≤(UpperOpenMathUnmarkedCrossResources.crossEdges n L G A N).card at cone
  have coneX : 2*A.card≤∑ p∈P,x p := by
    rw [xsum,degreeFrom_sum n L G A N aNonfull]
    exact cone
  exact ⟨ha,had,hfive,hext,hx,hfull,hbalanced,capacity,coneX⟩

theorem certificate_two_third_core_weight {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (triples : ∀ p∈core n L, (supports n L p).card=3) :
    let G := fun a => ofPredicate n L (tri a) hL (ht a)
    0≤3*(∑ p∈core n L, (6-2*(ordinaryDegree n L G p : ℤ)-coreDegree n L G p))+
      4*((unmarkedFullTwoCapSet n L hL hn tri ht).card : ℤ)+
      3*((core n L).filter (fun p => ordinaryDegree n L G p=1 ∧ coreDegree n L G p=5)).card := by
  have data := certificate_recipient_data n L hL hn tri hi ht triples
  exact UpperOpenMathTwoThirdCurvatureWeights.finite_two_third_curvature
    (core n L) (ordinaryDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)))
    (coreDegree n L (fun a => ofPredicate n L (tri a) hL (ht a))) (markedCount n L hL hn tri ht)
    (recipientCount n L hL hn tri ht) data.ha data.had data.hfive data.hext data.hx data.hfull
    data.hbalanced data.capacity data.cone

theorem certificate_two_third_defect_bound {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (triples : ∀ p∈core n L, (supports n L p).card=3) :
    let G := fun a => ofPredicate n L (tri a) hL (ht a)
    6*((n : ℤ)*(n-2)-3*Fintype.card α)+
      4*((unmarkedFullTwoCapSet n L hL hn tri ht).card : ℤ)+
      3*((core n L).filter (fun p => ordinaryDegree n L G p=1 ∧ coreDegree n L G p=5)).card≥
      6*(UpperEdgeInventory.edges n L\usedEdges G).card := by
  classical
  let G := fun a => ofPredicate n L (tri a) hL (ht a)
  have weighted := certificate_two_third_core_weight n L hL hn tri hi ht triples
  dsimp only at weighted
  have oneNat := UpperOpenMathCoreDoubleCount.one_core_incidence_sum n L hL tri hi ht
  have one : (∑ p∈core n L,(ordinaryDegree n L G p : ℤ))=(oneCoreEdges n L G).card := by exact_mod_cast oneNat
  have twoNat := UpperOpenMathCoreDoubleCount.two_core_incidence_sum n L hL tri ht
  have two : (∑ p∈core n L,(coreDegree n L G p : ℤ))=2*((twoCoreEdges n L G).card : ℤ) := by exact_mod_cast twoNat
  have sumW : (∑ p∈core n L,(6-2*(ordinaryDegree n L G p : ℤ)-coreDegree n L G p))=
      6*((core n L).card : ℤ)-2*(oneCoreEdges n L G).card-2*(twoCoreEdges n L G).card := by
    simp only [sum_sub_distrib,← mul_sum,sum_const,nsmul_eq_mul]
    rw [one,two]
    ring
  have sumLoss : (∑ p∈core n L,(supports n L p).card*((supports n L p).card-2 : ℤ))=
      3*((core n L).card : ℤ) := by
    calc
      _=∑ _p∈core n L,(3 : ℤ) := sum_congr rfl (fun p hp => by rw [triples p hp]; norm_num)
      _=_ := by simp [sum_const,nsmul_eq_mul,mul_comm]
  have defect := defect_identity n L hL hn tri hi ht
  dsimp only at defect ⊢
  rw [sumLoss] at defect
  rw [sumW] at weighted
  linarith

#print axioms certificate_balanced_anti_degree_zero
#print axioms certificate_recipient_data
#print axioms certificate_two_third_defect_bound
end Kobon.UpperOpenMathTwoThirdCurvature
