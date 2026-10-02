import Kobon.BBLRecursiveChoice
import Kobon.BBLVisibleSeed
import Kobon.BBLNextBoundary
import Kobon.BBLRightmost
import Kobon.BBLVisibleAssembly
import Kobon.BBLVisibleReindex

/-! Simultaneous triangle and maximal visible-wedge gain in the actual pencil. -/
namespace Kobon.BBLEvenStep
open Real Exterior BBLExtrema BBLAnalytic BBLIntersection BBLPencilRegularity
  BBLCrossingCoordinates BBLRealization BBLRealizedPencil BBLCanonicalPencil
  BBLRowGeometry BBLCentral BBLRightmost BBLNextBoundary BBLVisibleSeed
  BBLRecursiveChoice BBLVisibleAssembly BBLProjection Filter
open scoped Topology

theorem visible_retained_eventually (r : Nat) (ε : ℝ) (m : Nat→ℝ) (δ : ℝ) (w : Line ℝ)
    (hp : NoParallel (4*r+1) (oldArrangement r ε m))
    (hs : NoConcurrent (4*r+1) (oldArrangement r ε m))
    (hw : Admissible (4*r+1) (oldArrangement r ε m) w)
    (t : Triple) (ht : VisiblePair (4*r+1) (oldArrangement r ε m) w t) (hi : t.i≠0) :
    ∀ᶠ κ in 𝓝 (0:ℝ), VisiblePair (8*r+1) (arrangement r ε m δ κ) w (shift r t) := by
  let old := oldArrangement r ε m
  let D := direction r δ
  have hh := BBLPersistence.visible_preserved_eventually (4*r+1) (4*r) old D w hp hs hw t ht
    ⟨0,by omega⟩ (by dsimp; omega) (by have := ht.1; dsimp; omega)
  apply hh.mono
  intro κ hk
  rw [arrangement_eq_rotate_pencil]
  have hz := Reindex.rotate_visible (8*r+1) (BBLPersistence.pencilAppend (4*r+1) old D 0 κ)
    w ⟨t.i,t.j,8*r+1⟩ (by simpa only [show 4*r+1+4*r=8*r+1 by omega] using hk)
      (by change 0<t.i; omega)
  exact hz

theorem canonical_visible_step (r T V : Nat) (hr : 5≤r) (ε : ℝ)
    (hε0 : 0<ε) (hε : ε<tan (alpha r/2)) (w : Line ℝ) (hwa : 0<w.a)
    (s : VisibleSeed r T V ε w) :
    ∃ δ κ : ℝ, 0<δ ∧ 0<κ ∧
      NoParallel (8*r+1) (arrangement r ε s.slopes δ κ) ∧
      NoConcurrent (8*r+1) (arrangement r ε s.slopes δ κ) ∧
      CrossingOrder r (arrangement r ε s.slopes δ κ) xDirection ∧
      (0 < (intersection (arrangement r ε s.slopes δ κ (2*r-1))
        (arrangement r ε s.slopes δ κ (2*r))).2) ∧
      (∀ j, j<8*r-1 → TrianglePredicate (8*r+1)
        (arrangement r ε s.slopes δ κ) (BBLNextSaturation.gapTriangle r j)) ∧
      Admissible (8*r+1) (arrangement r ε s.slopes δ κ) w ∧
      (∀ i, i≤4*r → 0<w.a+w.b*auxSlope r δ κ i) ∧
      ∃ ts vs : List Triple, ts.Nodup ∧ vs.Nodup ∧
        (∀ t∈ts, TrianglePredicate (8*r+1) (arrangement r ε s.slopes δ κ) t) ∧
        (∀ t∈vs, VisiblePair (8*r+1) (arrangement r ε s.slopes δ κ) w t) ∧
        T+(4*r)^2≤ts.length ∧ V+2*r≤vs.length := by
  let c : Fin (4*r) := ⟨3*r-1,by omega⟩
  have hd := good_delta_eventually r hr ε hε0 hε
  have hm := perturbed_strict_maximum r hr c (by dsimp [c]; omega)
  have hdall : ∀ᶠ δ in 𝓝 (0:ℝ), 0<δ → GoodDelta r ε δ ∧
      (∀ i : Fin (4*r), i≠c → h r i δ<h r c δ) := by
    filter_upwards [hd,hm] with δ hd hm
    exact fun hδ => ⟨hd hδ,hm⟩
  obtain ⟨δ,hδ,hgood,hmax⟩ := positive_eventually_exists _ hdall
  let L := fun κ => arrangement r ε s.slopes δ κ
  have hc := canonical_eventually r T hr ε hε0 hε s.slopes s.no_parallel s.no_concurrent
    s.saturated s.central_positive s.triangles s.nodup s.valid s.count δ hgood
  have hpdir := positive_directions_eventually r δ w hwa
  have hrow := canonical_row_eventually r hr ε δ s.slopes hδ s.right_positive
    (fun i hi => hmax i (by intro he; exact hi (congrArg Fin.val he))) s.right_boundary
  have hret : ∀ᶠ κ in 𝓝 (0:ℝ), ∀ t∈s.visible, t.i≠0 →
      VisiblePair (8*r+1) (L κ) w (shift r t) := by
    apply BBLOldRetention.eventually_list
    intro t ht
    by_cases hi : t.i=0
    · exact Filter.Eventually.of_forall (fun _ hn => (hn hi).elim)
    · exact (visible_retained_eventually r ε s.slopes δ w s.no_parallel s.no_concurrent
        s.admissible t (s.visible_valid t ht) hi).mono (fun _ hh _ => hh)
  have hall : ∀ᶠ κ in 𝓝 (0:ℝ), 0<κ →
      NoParallel (8*r+1) (L κ) ∧ NoConcurrent (8*r+1) (L κ) ∧
      CrossingOrder r (L κ) xDirection ∧
      (0 < (intersection (L κ (2*r-1)) (L κ (2*r))).2) ∧
      (∀ j, j<8*r-1 → TrianglePredicate (8*r+1) (L κ) (BBLNextSaturation.gapTriangle r j)) ∧
      Admissible (8*r+1) (L κ) w ∧ (∀ i, i≤4*r → 0<w.a+w.b*auxSlope r δ κ i) ∧
      ∃ ts vs : List Triple, ts.Nodup ∧ vs.Nodup ∧
        (∀ t∈ts, TrianglePredicate (8*r+1) (L κ) t) ∧
        (∀ t∈vs, VisiblePair (8*r+1) (L κ) w t) ∧
        T+(4*r)^2≤ts.length ∧ V+2*r≤vs.length := by
    filter_upwards [hc,hpdir,hrow,hret] with κ hc hpdir hrow hret
    intro hκ
    obtain ⟨hp,hs,ho,_,hcenter,hsat,ts,hn,ht,hcount⟩ := hc hκ
    have hw := admissible_of_directions r ε s.slopes δ κ w s.admissible hpdir
    have how := crossing_order_oblique r ε s.slopes δ κ w hp hpdir ho
    have hR : ∀ i : Fin (8*r+1), i.val≠4*r-1 → i.val≠7*r-1 →
        projection w (intersection (L κ (4*r-1)) (L κ i)) <
          projection w (intersection (L κ (4*r-1)) (L κ (7*r-1))) := by
      intro i hiR hiC
      have hdR := det_ne_of_ne (8*r+1) (L κ) hp ⟨4*r-1,by omega⟩ i
        (by intro he; exact hiR (congrArg Fin.val he).symm)
      have hdC := hp ⟨4*r-1,by omega⟩ ⟨7*r-1,by omega⟩ (by change 4*r-1<7*r-1; omega)
      have hpR := intersection_on_left (L κ (4*r-1)) (L κ i) hdR
      have hpC := intersection_on_left (L κ (4*r-1)) (L κ (7*r-1)) hdC
      have hgraph : L κ (4*r-1)=graphLine (s.slopes (4*r-1)) (oldIntercept r ε (4*r-1)) :=
        arrangement_old r ε s.slopes δ κ (4*r-1) (by omega)
      have hpR' : affineEval (graphLine (s.slopes (4*r-1)) (oldIntercept r ε (4*r-1)))
          (intersection (L κ (4*r-1)) (L κ i))=0 := by rw [← hgraph]; exact hpR
      have hpC' : affineEval (graphLine (s.slopes (4*r-1)) (oldIntercept r ε (4*r-1)))
          (intersection (L κ (4*r-1)) (L κ (7*r-1)))=0 := by rw [← hgraph]; exact hpC
      exact graph_projection_strict_mono _ _ w _ _ hpR' hpC' s.right_direction (hrow hκ i hiR hiC)
    have hvcenter := BBLVisible.central_visible r (by omega) (L κ) w hp hs hw how hR
    obtain ⟨vs,hvn,hvv,hvc⟩ := visible_gain r V (by omega)
      (oldArrangement r ε s.slopes) (L κ) w s.visible s.visible_nodup s.no_parallel
      s.no_concurrent s.admissible s.visible_valid s.visible_count hp hs hw how hret hvcenter
    exact ⟨hp,hs,ho,hcenter,hsat,hw,hpdir,ts,vs,hn,hvn,ht,hvv,hcount,hvc⟩
  obtain ⟨κ,hκ,hk⟩ := positive_eventually_exists _ hall
  exact ⟨δ,κ,hδ,hκ,hk⟩

#print axioms canonical_visible_step
end Kobon.BBLEvenStep
