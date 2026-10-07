import Kobon.UpperOpenMathTripleCurvatureWeights
import Kobon.UpperOpenMathClosedExtremal

/-! A full fan of core-ended shared rays meets both open sides of every
line through its center. Thus a finite closed set cannot consist entirely
of such fans. The endpoints and closure are extracted from actual triangles. -/
namespace Kobon.UpperOpenMathFullCoreFans
open Cells FanGeometry UpperFan UpperVertexBudget UpperTriangleIncidence
  UpperSharedIncidence UpperCoreExtraction UpperOpenMathRadialOrder
  UpperOpenMathActualFans UpperOpenMathCapHeavyTriples UpperOpenMathCoreComponents Finset

theorem core_full {n r : ℕ} [NeZero (2*r)] {L : ℕ → Line ℝ}
    (f : UpperFan.Sectors n r L) (hc : f.coreShared.card=2*r) :
    f.coreShared=univ ∧ f.triangular=univ := by
  classical
  have hfull : f.coreShared=univ := by
    apply eq_of_subset_of_card_le (subset_univ _)
    simpa using hc.ge
  refine ⟨hfull,?_⟩
  apply eq_of_subset_of_card_le (subset_univ _)
  have hs : f.coreShared⊆f.triangular :=
    (sdiff_subset : f.coreShared⊆f.shared).trans (filter_subset _ _)
  rw [hfull] at hs
  exact card_le_card hs

theorem certificate_full_core_neighbors_surround {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (c : Point) (hc : c∈core n L) (w : Line ℝ)
    (hw : affineEval w c=0) (valid : w.a≠0 ∨ w.b≠0)
    (full : coreDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) c=
      2*(supports n L c).card) :
    ∃ q∈core n L, {c,q}∈twoCoreEdges n L (fun a => ofPredicate n L (tri a) hL (ht a)) ∧
      affineEval w q<0 := by
  classical
  have hr := core_multiplicity n L hL hc
  letI : NeZero (2*(supports n L c).card) := ⟨by omega⟩
  let D := atPoint n L hL hn c
  let f := fan n L hL hn tri ht c (mem_filter.mp hc).1 D (by omega)
  have hf : f.coreShared.card=2*(supports n L c).card := by
    rw [fan_core_card n L hL hn tri ht c (mem_filter.mp hc).1 D (by omega) hi hc]
    exact full
  obtain ⟨all,triangles⟩ := core_full f hf
  obtain ⟨z,_,negative⟩ := UpperFanSupport.Sectors.exists_negative_core_endpoint
    f triangles (fan_positive n L hL hn tri ht c (mem_filter.mp hc).1 D (by omega)) w hw valid
  have hz : z∈f.coreShared := by rw [all]; exact mem_univ z
  exact ⟨f.point z,fan_core_endpoint n L hL hn tri ht c (mem_filter.mp hc).1 D (by omega) hi hc z hz,
    (fan_core_iff n L hL hn tri ht c (mem_filter.mp hc).1 D (by omega) hi hc z).mp hz,negative⟩

theorem certificate_closed_full_core_impossible {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (P : Finset Point) (sub : P⊆core n L) (nonempty : P.Nonempty)
    (closed : SharedCoreClosed n L (fun a => ofPredicate n L (tri a) hL (ht a)) P)
    (full : ∀ p∈P, coreDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) p=
      2*(supports n L p).card) : False := by
  classical
  obtain ⟨p,hp,hmax⟩ := exists_max_image P (fun p : Point => p.1) nonempty
  let w : Line ℝ := ⟨-1,0,-p.1⟩
  have wp : affineEval w p=0 := by dsimp [w,affineEval]; ring
  have valid : w.a≠0 ∨ w.b≠0 := Or.inl (by norm_num [w])
  obtain ⟨q,hq,edge,neg⟩ := certificate_full_core_neighbors_surround
    n L hL hn tri hi ht p (sub hp) w wp valid (full p hp)
  have hqP : q∈P := closed {p,q} edge p (by simp) hp (by simp)
  have hle := hmax q hqP
  dsimp [w,affineEval] at neg
  linarith

#print axioms core_full
#print axioms certificate_full_core_neighbors_surround
#print axioms certificate_closed_full_core_impossible
end Kobon.UpperOpenMathFullCoreFans
