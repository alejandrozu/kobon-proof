import Kobon.BBLCanonicalPencil
import Kobon.BBLCapRetention
import Kobon.BBLOldRetention
import Kobon.BBLAlternation

/-! Actual one-step BBL geometric doubling from a saturated tangent-grid seed.
Every crossing order and every retained cap is proved for real lines. This
does not assert that the resulting witness satisfies an iterative seed invariant. -/
namespace Kobon.BBLDoubling
open Real Exterior BBLExtrema BBLAnalytic BBLIntersection BBLPencilRegularity
  BBLCrossingCoordinates BBLRealization BBLRealizedPencil BBLCanonicalPencil BBLRowGeometry
  BBLCapBridge BBLCentralPersistence BBLCapRetention BBLOldRetention BBLAssembly Filter
open scoped Topology

theorem doubling (r T : Nat) (hr : 5 ≤ r) (ε : ℝ)
    (hε0 : 0 < ε) (hε : ε < tan (alpha r/2)) (m : Nat → ℝ)
    (hp : NoParallel (4*r+1) (oldArrangement r ε m))
    (hs : NoConcurrent (4*r+1) (oldArrangement r ε m))
    (hsaturated : ∀ j, j < 4*r-1 →
      TrianglePredicate (4*r+1) (oldArrangement r ε m) ⟨0,j+1,j+2⟩)
    (hcenter : 0 < (intersection (oldArrangement r ε m (2*r))
      (oldArrangement r ε m (2*r+1))).2)
    (ts : List Triple) (hn : ts.Nodup)
    (ht : ∀ t∈ts, TrianglePredicate (4*r+1) (oldArrangement r ε m) t)
    (hcount : T ≤ ts.length) : SimpleLowerBound (8*r+1) (T+(4*r)^2) := by
  let old := oldArrangement r ε m
  have h0 : old 0=graphLine 0 0 := by simp [old,oldArrangement]
  have hgraph : ∀ j < 4*r, old (j+1)=graphLine (m j) (oldIntercept r ε j) := by
    intro j _
    simp [old,oldArrangement]
  have hordered := old_intercepts_strict r hr ε hε0 hε
  have halt := BBLAlternation.saturated_alternation r (by omega) old hp hs m
    (oldIntercept r ε) h0 hgraph (fun j hj => hordered j (j+1) (by omega) hj)
    hsaturated hcenter
  obtain ⟨δ,hδ⟩ := good_delta_exists r hr ε hε0 hε
  let D := direction r δ
  let L := fun κ => arrangement r ε m δ κ
  have he := realized_pencil_eventually r hr ε hε0 hε m δ hδ
    (old_slopes_ne_zero r ε m hp) (old_slopes_distinct r ε m hp) hs
  have hrot (κ : ℝ) : L κ=Reindex.rotate (8*r+1)
      (BBLPersistence.pencilAppend (4*r+1) old D 0 κ) :=
    arrangement_eq_rotate_pencil r ε m δ κ
  have holdline (κ : ℝ) (j : Nat) (hj : j < 4*r) : L κ j=old (j+1) := by
    rw [show L κ j=arrangement r ε m δ κ j from rfl,arrangement_old r ε m δ κ j hj,hgraph j hj]
  have hnewgraph (κ : ℝ) : ∀ j < 4*r,
      L κ (4*r+j)=graphLine (κ*slopeFactor δ (newIntercept r j)) (newIntercept r j) := by
    intro j hj
    exact arrangement_new r ε m δ κ j hj
  have hnewzero (κ : ℝ) : L κ (8*r)=graphLine 0 0 := arrangement_zero r ε m δ κ
  have hcaps : ∀ j, j < 4*r-1 → j ≠ 2*r-1 → ∀ᶠ κ in 𝓝 (0:ℝ), 0 < κ →
      CanonicalEndpointSigns r j (Reindex.rotate (8*r+1)
        (BBLPersistence.pencilAppend (4*r+1) old D 0 κ)) := by
    intro j hj hc
    apply he.mono
    intro κ hh hκ
    obtain ⟨hpn,hsn,ho⟩ := hh (ne_of_gt hκ)
    rw [← hrot]
    apply canonical_endpoint_signs r j (by omega) hj hc (L κ) xDirection
      (fun i => κ*slopeFactor δ (newIntercept r i)) (newIntercept r)
      hpn hsn (admissible_x r ε m δ κ) ho (hnewgraph κ) (hnewzero κ)
      (new_slopes_neg r hr δ κ hδ.1 hκ) (new_slopes_pos r hr δ κ hδ.1 hκ)
      (new_intercepts_strict r hr)
    · norm_num [xDirection]
    · rw [holdline κ j (by omega),holdline κ (j+1) (by omega)]
      have ha := halt j hj
      exact ⟨ha.1,fun h => ha.2 (by omega)⟩
  have hcentral : ∀ᶠ κ in 𝓝 (0:ℝ), 0 < κ → CanonicalCentralSigns r
      (Reindex.rotate (8*r+1) (BBLPersistence.pencilAppend (4*r+1) old D 0 κ)) := by
    apply he.mono
    intro κ hh hκ
    obtain ⟨hpn,_,ho⟩ := hh (ne_of_gt hκ)
    rw [← hrot]
    apply canonical_central_signs r (by omega) (L κ) xDirection
      (fun i => κ*slopeFactor δ (newIntercept r i)) (newIntercept r)
      hpn ho (hnewgraph κ) (hnewzero κ)
      (new_slopes_neg r hr δ κ hδ.1 hκ) (new_slopes_pos r hr δ κ hδ.1 hκ)
    · norm_num [xDirection]
    · rw [holdline κ (2*r-1) (by omega),holdline κ (2*r) (by omega)]
      simpa only [show 2*r-1+1=2*r by omega] using hcenter
  have hret := all_replaced_positive_eventually r old D hp hs ts ht
    (fun t hmem hti => cap_retained_eventually r (by omega) old D m
      (oldIntercept r ε) hp hs h0 hgraph hordered hcaps hcentral t (ht t hmem) hti)
  have hall : ∀ᶠ κ in 𝓝 (0:ℝ), 0 < κ →
      NoParallel (8*r+1) (L κ) ∧ NoConcurrent (8*r+1) (L κ) ∧
      CrossingOrder r (L κ) xDirection ∧
      ∀ t∈ts, TrianglePredicate (8*r+1) (L κ) (replace r t) := by
    filter_upwards [he,hret] with κ he hr
    intro hk
    obtain ⟨hpn,hsn,ho⟩ := he (ne_of_gt hk)
    refine ⟨hpn,hsn,ho,?_⟩
    simpa only [hrot] using hr hk
  obtain ⟨κ,_,hκ⟩ := positive_eventually_exists _ hall
  exact doubling_bound r T (by omega) old (L κ) xDirection ts hn ht hcount
    hκ.1 hκ.2.1 (admissible_x r ε m δ κ) hκ.2.2.1 hκ.2.2.2

#print axioms doubling
end Kobon.BBLDoubling
