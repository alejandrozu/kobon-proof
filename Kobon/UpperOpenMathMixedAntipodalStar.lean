import Kobon.UpperOpenMathMixedStarWeights

/-! A closed five-point antipodal star pays its two-cap correction even
when its four outer cores have higher multiplicity. -/
namespace Kobon.UpperOpenMathMixedAntipodalStar
open Cells FanGeometry UpperFan UpperVertexBudget UpperTriangleIncidence UpperSharedIncidence
  UpperCoreExtraction UpperOpenMathCapHeavyTriples UpperOpenMathCoreComponents
  UpperOpenMathAntipodalTwoCapChart UpperOpenMathAntipodalStarDegree
  UpperOpenMathAntipodalStarWeights UpperOpenMathMixedDegreeThree UpperOpenMathMixedStarWeights Finset
open scoped BigOperators
set_option maxHeartbeats 1000000

theorem certificate_mixed_antipodal_star_cost {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (f : UpperFan.Sectors n 3 L)
    (data : AntipodalData (fun a => ofPredicate n L (tri a) hL (ht a)) f)
    (P : Finset Point) (sub : P⊆core n L) (hc : f.center∈P) (small : P.card≤5)
    (closed : SharedCoreClosed n L (fun a => ofPredicate n L (tri a) hL (ht a)) P)
    (rc : (supports n L f.center).card=3)
    (ac : ordinaryDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) f.center=2)
    (dc : coreDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) f.center=4) :
    1+higherSurplusOn n L P≤componentCost n L (fun a => ofPredicate n L (tri a) hL (ht a)) P := by
  classical
  let G := fun a => ofPredicate n L (tri a) hL (ht a)
  let W := mixedWeight n L G
  have properties (z : ZMod (2*3)) (hz : z∈f.coreShared) :=
    certificate_weight_neighbor_full_two_cap n L hL hn tri hi ht (f.point z) f.center
      (data.core_endpoint z hz) (sub hc) rc ac dc
      (by simpa only [pair_comm] using core_edge_of_label G f data.toFullData z hz)
      ((certificate_outer_degrees n L hL tri ht f data P hc small closed z hz).trans (by omega))
  have degree (z : ZMod (2*3)) (hz : z∈f.coreShared) : coreDegree n L G (f.point z)≤2 :=
    certificate_outer_degrees n L hL tri ht f data P hc small closed z hz
  have star := closed_star_eq G f data.toFullData P hc small closed
  have no : f.center∉f.coreShared.image f.point := by
    intro h
    obtain ⟨z,_,hz⟩ := mem_image.mp h
    exact data.noncentral z hz
  have sumW : (∑ p∈P, W p)=W f.center+∑ z∈f.coreShared, W (f.point z) := by
    rw [star,sum_insert no,sum_image]
    intro a _ b _ h
    exact data.injective h
  have wc : W f.center=-2 := by
    dsimp [W,mixedWeight]
    rw [rc,ac,dc]
    norm_num
  have outerLower : 4≤∑ z∈f.coreShared, W (f.point z) := by
    by_cases high : ∃ z∈f.coreShared, 4≤(supports n L (f.point z)).card
    · obtain ⟨z,hz,hhigh⟩ := high
      have lower : 6≤W (f.point z) := (properties z hz).2.2 (degree z hz) |>.2.2 hhigh
      have ge := single_le_sum (fun k hk => (properties k hk).1) hz
      change W (f.point z)≤∑ k∈f.coreShared, W (f.point k) at ge
      omega
    · have triples (p : Point) (hp : p∈P) : (supports n L p).card=3 := by
        rw [star] at hp
        rcases mem_insert.mp hp with hp|hp
        · simpa only [hp] using rc
        · obtain ⟨z,hz,rfl⟩ := mem_image.mp hp
          have r := core_multiplicity n L hL (data.core_endpoint z hz)
          have nohigh : ¬(4≤(supports n L (f.point z)).card) := fun hh => high ⟨z,hz,hh⟩
          omega
      have pairBound (g : UpperFan.Sectors n 3 L) (dg : AntipodalData G g) (gc : g.center=f.center) :
          2≤W (g.point 1)+W (g.point 2) := by
        have gcp : g.center∈P := by simpa only [gc] using hc
        have gr : (supports n L g.center).card=3 := by simpa only [gc] using rc
        have ga : ordinaryDegree n L G g.center=2 := by simpa only [gc] using ac
        have gd : coreDegree n L G g.center=4 := by simpa only [gc] using dc
        have prop (z : ZMod (2*3)) (hz : z∈g.coreShared) :=
          certificate_weight_neighbor_full_two_cap n L hL hn tri hi ht (g.point z) g.center
            (dg.core_endpoint z hz) (sub gcp) gr ga gd
            (by simpa only [pair_comm] using core_edge_of_label G g dg.toFullData z hz)
            ((certificate_outer_degrees n L hL tri ht g dg P gcp small closed z hz).trans (by omega))
        have one := (prop 1 (by rw [dg.core_eq]; simp)).2.2
          (certificate_outer_degrees n L hL tri ht g dg P gcp small closed 1 (by rw [dg.core_eq]; simp))
        have two := (prop 2 (by rw [dg.core_eq]; simp)).2.2
          (certificate_outer_degrees n L hL tri ht g dg P gcp small closed 2 (by rw [dg.core_eq]; simp))
        change (W (g.point 1)=0 ∨ 2≤W (g.point 1)) ∧ _ at one
        change (W (g.point 2)=0 ∨ 2≤W (g.point 2)) ∧ _ at two
        by_cases z1 : W (g.point 1)=0
        · have t1 := one.2.1 z1
          by_cases z2 : W (g.point 2)=0
          · have t2 := two.2.1 z2
            exact False.elim (certificate_first_pair_not_zero_local n L hL hn tri hi ht P triples
              g dg sub gcp small closed ga t1.2.1 t1.2.2 t2.2.1 t2.2.2)
          · omega
        · omega
      have first := pairBound f data rfl
      have second := pairBound (UpperOpenMathRotation.Sectors.shift f 3) (shift_three_data G f data) rfl
      have i4 : (3 : ZMod (2*3))+1=4 := by decide
      have i5 : (3 : ZMod (2*3))+2=5 := by decide
      change 2≤W (f.point (3+1))+W (f.point (3+2)) at second
      rw [i4,i5] at second
      rw [data.core_eq,sum_insert (by decide),sum_insert (by decide),sum_insert (by decide),sum_singleton]
      omega
  have identity := mixed_weight_sum n L G P closed
  change (∑ p∈P, W p)=2*(componentCost n L G P-higherSurplusOn n L P) at identity
  rw [sumW,wc] at identity
  change 1+higherSurplusOn n L P≤componentCost n L G P
  linarith

#print axioms certificate_mixed_antipodal_star_cost
end Kobon.UpperOpenMathMixedAntipodalStar
