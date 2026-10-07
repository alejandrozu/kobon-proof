import Kobon.UpperOpenMathTripleCurvature
import Kobon.UpperOpenMathSmallCoreRigidity

/-! Necessary local obstructions to perfect and near-perfect counts.
These statements do not rule the exceptional full fans out globally. -/
namespace Kobon.UpperOpenMathTripleCurvatureConsequences
open Cells FanGeometry UpperVertexBudget UpperTriangleIncidence UpperSharedIncidence
  UpperCoreExtraction UpperOpenMathCapHeavyTriples UpperOpenMathCoreComponents
  UpperOpenMathTripleCurvature Finset

theorem certificate_no_bad_fan_upper {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (triples : ∀ p∈core n L, (supports n L p).card=3)
    (good : ∀ p∈core n L,
      ¬(ordinaryDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) p=2 ∧
         coreDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) p=4) ∧
      ¬(ordinaryDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) p=1 ∧
         coreDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) p=5)) :
    let G := fun a => ofPredicate n L (tri a) hL (ht a)
    3*(Fintype.card α : ℤ)+(UpperEdgeInventory.edges n L\usedEdges G).card+
      coreComponentCount n L G≤(n : ℤ)*(n-2) := by
  classical
  let G := fun a => ofPredicate n L (tri a) hL (ht a)
  have bound := certificate_triple_curvature_upper n L hL hn tri hi ht triples
  have hz : badCurvature n L G=0 := by
    unfold badCurvature badCurvatureOn
    apply sum_eq_zero
    intro p hp
    dsimp only [G]
    simp only [UpperOpenMathTripleCurvatureWeights.badWeight,if_neg (good p hp).1,if_neg (good p hp).2]
  change 3*(Fintype.card α : ℤ)+(UpperEdgeInventory.edges n L\usedEdges G).card+
    coreComponentCount n L G≤(n : ℤ)*(n-2)+badCurvature n L G at bound
  rw [hz,add_zero] at bound
  exact bound

theorem certificate_no_bad_fan_perfect_simple {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (triples : ∀ p∈core n L, (supports n L p).card=3)
    (good : ∀ p∈core n L,
      ¬(ordinaryDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) p=2 ∧
         coreDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) p=4) ∧
      ¬(ordinaryDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) p=1 ∧
         coreDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) p=5))
    (perfect : (n : ℤ)*(n-2)=3*Fintype.card α) : NoConcurrent n L := by
  classical
  let G := fun a => ofPredicate n L (tri a) hL (ht a)
  have bound := certificate_no_bad_fan_upper n L hL hn tri hi ht triples good
  change 3*(Fintype.card α : ℤ)+(UpperEdgeInventory.edges n L\usedEdges G).card+
    coreComponentCount n L G≤(n : ℤ)*(n-2) at bound
  rw [perfect] at bound
  have hu : (0 : ℤ)≤(UpperEdgeInventory.edges n L\usedEdges G).card := by positivity
  have hc : coreComponentCount n L G=0 := by omega
  exact (UpperOpenMathDegreeBudgets.core_empty_iff_simple n L hL).mp
    ((UpperOpenMathSmallCoreRigidity.component_count_zero_iff n L G).mp hc)

theorem certificate_perfect_nonsimple_has_bad_fan {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (triples : ∀ p∈core n L, (supports n L p).card=3)
    (perfect : (n : ℤ)*(n-2)=3*Fintype.card α) (nonsimple : ¬NoConcurrent n L) :
    ∃ p∈core n L,
      (ordinaryDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) p=2 ∧
       coreDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) p=4) ∨
      (ordinaryDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) p=1 ∧
       coreDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) p=5) := by
  classical
  by_contra h
  push_neg at h
  apply nonsimple
  apply certificate_no_bad_fan_perfect_simple n L hL hn tri hi ht triples _ perfect
  intro p hp
  exact ⟨fun hb => (h p hp).1 hb.1 hb.2,fun hb => (h p hp).2 hb.1 hb.2⟩

#print axioms certificate_no_bad_fan_upper
#print axioms certificate_no_bad_fan_perfect_simple
#print axioms certificate_perfect_nonsimple_has_bad_fan
end Kobon.UpperOpenMathTripleCurvatureConsequences
