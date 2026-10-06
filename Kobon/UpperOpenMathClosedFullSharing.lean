import Kobon.UpperOpenMathFullSharing

/-! A finite nonempty actual shared-core component cannot have all shared
rays occupied. Ordinary shared tips are allowed, at any multiplicity. -/
namespace Kobon.UpperOpenMathClosedFullSharing
open Cells FanGeometry UpperVertexBudget UpperTriangleIncidence UpperSharedIncidence
  UpperCoreExtraction UpperOpenMathCoreComponents UpperOpenMathCapHeavyTriples Finset

theorem certificate_closed_full_sharing_impossible {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (P : Finset Point) (sub : P⊆core n L) (nonempty : P.Nonempty)
    (closed : SharedCoreClosed n L (fun a => ofPredicate n L (tri a) hL (ht a)) P)
    (full : ∀ p∈P,
      ordinaryDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) p+
      coreDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) p=
      2*(supports n L p).card) : False := by
  classical
  obtain ⟨p,hp,hmax⟩ := exists_max_image P (fun p : Point => p.1) nonempty
  let w : Line ℝ := ⟨-1,0,-p.1⟩
  have wp : affineEval w p=0 := by dsimp [w,affineEval]; ring
  have valid : w.a≠0 ∨ w.b≠0 := Or.inl (by norm_num [w])
  obtain ⟨q,hq,edge,neg⟩ := UpperOpenMathFullSharing.certificate_full_sharing_neighbors_surround
    n L hL hn tri hi ht p (sub hp) w wp valid (full p hp)
  have hqP : q∈P := closed {p,q} edge p (by simp) hp (by simp)
  have hle := hmax q hqP
  dsimp [w,affineEval] at neg
  linarith

#print axioms certificate_closed_full_sharing_impossible
end Kobon.UpperOpenMathClosedFullSharing
