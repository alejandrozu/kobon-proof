import Kobon.UpperOpenMathActualFans
import Kobon.UpperCoreBoundary

/-!
# Actual exposed cores cannot have extremal ordinary-sharing degree

The supporting-half-plane obstruction is now applied to the fully extracted
fans of actual certificate families. In particular every nonempty finite
core has at least one nonexceptional point. No local fan or endpoint map is
supplied as a premise of the final arrangement statements.
-/
namespace Kobon.UpperOpenMathSupportedCores
open Cells FanGeometry UpperVertexBudget UpperTriangleIncidence UpperSharedIncidence
  UpperCoreExtraction UpperOpenMathRadialOrder UpperOpenMathActualFans Finset

section Certificate
variable {α : Type*} [Fintype α]
  (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
  (tri : α → Triple) (hi : Function.Injective tri)
  (ht : ∀ a, TrianglePredicate n L (tri a)) (c : Point) (hcore : c∈core n L)

include hn hi hcore in
theorem certificate_extremal_neighbor_count
    (extremal : 2*(supports n L c).card-3≤
      ((oneCoreEdges n L (fun a => ofPredicate n L (tri a) hL (ht a))).filter (fun e => c∈e)).card) :
    ((twoCoreEdges n L (fun a => ofPredicate n L (tri a) hL (ht a))).filter (fun e => c∈e)).card=3 := by
  classical
  have hr := core_multiplicity n L hL hcore
  letI : NeZero (2*(supports n L c).card) := ⟨by omega⟩
  let D := atPoint n L hL hn c
  have hc := (mem_filter.mp hcore).1
  rw [← fan_core_card n L hL hn tri ht c hc D (by omega) hi hcore]
  apply (fan n L hL hn tri ht c hc D (by omega)).core_shared_card_eq_three_of_extremal hr
  rw [fan_ordinary_card n L hL hn tri ht c hc D (by omega) hi hcore]
  exact extremal

include hn hi hcore in
theorem certificate_supported_core_bound (w : Line ℝ)
    (hw : affineEval w c=0) (valid : w.a≠0 ∨ w.b≠0)
    (support : ∀ p∈core n L, 0≤affineEval w p) :
    ((oneCoreEdges n L (fun a => ofPredicate n L (tri a) hL (ht a))).filter (fun e => c∈e)).card≤
      2*(supports n L c).card-4 := by
  classical
  have hr := core_multiplicity n L hL hcore
  letI : NeZero (2*(supports n L c).card) := ⟨by omega⟩
  let D := atPoint n L hL hn c
  have hc := (mem_filter.mp hcore).1
  rw [← fan_ordinary_card n L hL hn tri ht c hc D (by omega) hi hcore]
  apply UpperCoreBoundary.bound_at_supported_core
    (fan n L hL hn tri ht c hc D (by omega)) hr
    (fan_positive n L hL hn tri ht c hc D (by omega)) (core n L)
    (fan_core_endpoint n L hL hn tri ht c hc D (by omega) hi hcore) w hw valid support

include hn hi hcore in
theorem certificate_extremal_neighbors_surround (w : Line ℝ)
    (hw : affineEval w c=0) (valid : w.a≠0 ∨ w.b≠0)
    (extremal : 2*(supports n L c).card-3≤
      ((oneCoreEdges n L (fun a => ofPredicate n L (tri a) hL (ht a))).filter (fun e => c∈e)).card) :
    ∃ q∈core n L, {c,q}∈twoCoreEdges n L (fun a => ofPredicate n L (tri a) hL (ht a)) ∧
      affineEval w q<0 := by
  classical
  have hr := core_multiplicity n L hL hcore
  letI : NeZero (2*(supports n L c).card) := ⟨by omega⟩
  let D := atPoint n L hL hn c
  have hc := (mem_filter.mp hcore).1
  let f := fan n L hL hn tri ht c hc D (by omega)
  have hext : 2*(supports n L c).card-3≤f.ordinaryShared.card := by
    rw [fan_ordinary_card n L hL hn tri ht c hc D (by omega) hi hcore]
    exact extremal
  obtain ⟨z,hz,negative⟩ := UpperFanSupport.Sectors.extremal_core_not_in_halfplane
    f hr hext (fan_positive n L hL hn tri ht c hc D (by omega)) w hw valid
  exact ⟨f.point z,fan_core_endpoint n L hL hn tri ht c hc D (by omega) hi hcore z hz,
    (fan_core_iff n L hL hn tri ht c hc D (by omega) hi hcore z).mp hz,negative⟩

end Certificate

theorem finite_core_has_support (n : ℕ) (L : ℕ → Line ℝ) (hne : (core n L).Nonempty) :
    ∃ c∈core n L, ∃ w : Line ℝ, affineEval w c=0 ∧ (w.a≠0 ∨ w.b≠0) ∧
      ∀ p∈core n L, 0≤affineEval w p := by
  classical
  obtain ⟨c,hc,hmax⟩ := exists_max_image (core n L) (fun p : Point => p.1) hne
  let w : Line ℝ := ⟨-1,0,-c.1⟩
  refine ⟨c,hc,w,by dsimp [w,affineEval]; ring,Or.inl (by norm_num [w]),?_⟩
  intro p hp
  have hm := hmax p hp
  dsimp [w,affineEval]
  nlinarith

/-- A nonempty actual core contains an exposed, nonextremal point for every
selected certified triangle family. -/
theorem certificate_exists_nonextremal {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a)) (hne : (core n L).Nonempty) :
    ∃ c∈core n L,
      ((oneCoreEdges n L (fun a => ofPredicate n L (tri a) hL (ht a))).filter (fun e => c∈e)).card≤
        2*(supports n L c).card-4 := by
  obtain ⟨c,hc,w,hw,hvalid,hsupport⟩ := finite_core_has_support n L hne
  exact ⟨c,hc,certificate_supported_core_bound n L hL hn tri hi ht c hc w hw hvalid hsupport⟩

#print axioms certificate_supported_core_bound
#print axioms certificate_extremal_neighbor_count
#print axioms certificate_extremal_neighbors_surround
#print axioms certificate_exists_nonextremal
end Kobon.UpperOpenMathSupportedCores
