import Kobon.UpperOpenMathTwoTwoCore
import Kobon.UpperOpenMathPerfectRigidity

namespace Kobon.UpperOpenMathPerfectCoreCycle
open Cells FanGeometry UpperVertexBudget UpperTriangleIncidence UpperSharedIncidence
  UpperCoreExtraction UpperOpenMathCapHeavyTriples Finset

theorem certificate_perfect_degree_two_is_simple {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (degree : ∀ c∈core n L, coreDegree n L
      (fun a => ofPredicate n L (tri a) hL (ht a)) c≤2)
    (perfect : (n : ℤ)*(n-2)=3*Fintype.card α) : core n L=∅ := by
  have rigid := UpperOpenMathPerfectRigidity.certificate_perfect_local_rigidity
    n L hL hn tri hi ht degree perfect
  exact UpperOpenMathTwoTwoCore.certificate_two_two_core_empty n L hL hn tri hi ht
    (fun c hc => (rigid c hc).1) (fun c hc => (rigid c hc).2.1) (fun c hc => (rigid c hc).2.2)


#print axioms certificate_perfect_degree_two_is_simple
end Kobon.UpperOpenMathPerfectCoreCycle
