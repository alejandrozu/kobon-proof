import Kobon.BBLRecursiveWitness

/-! The actual BBL step retains its geometric coordinates and next-grid
saturation. Central retention is imposed independently of the counted list.
This is the geometric output needed by the recursive sorted-seed invariant. -/
namespace Kobon.BBLRecursiveChoice
open Real Exterior BBLExtrema BBLAnalytic BBLIntersection BBLPencilRegularity
  BBLCrossingCoordinates BBLRealization BBLRealizedPencil BBLCanonicalPencil BBLRowGeometry
  BBLCapBridge BBLCentralPersistence BBLCapRetention BBLOldRetention BBLAssembly Filter
open scoped Topology

theorem canonical_eventually (r T : Nat) (hr : 5 ≤ r) (ε : ℝ)
    (hε0 : 0 < ε) (hε : ε < tan (alpha r/2)) (m : Nat → ℝ)
    (hp : NoParallel (4*r+1) (oldArrangement r ε m))
    (hs : NoConcurrent (4*r+1) (oldArrangement r ε m))
    (hsaturated : ∀ j, j < 4*r-1 →
      TrianglePredicate (4*r+1) (oldArrangement r ε m) ⟨0,j+1,j+2⟩)
    (hcenter : 0 < (intersection (oldArrangement r ε m (2*r))
      (oldArrangement r ε m (2*r+1))).2)
    (ts : List Triple) (hn : ts.Nodup)
    (ht : ∀ t∈ts, TrianglePredicate (4*r+1) (oldArrangement r ε m) t)
    (hcount : T ≤ ts.length) (δ : ℝ) (hδ : GoodDelta r ε δ) :
    ∀ᶠ κ in 𝓝 (0:ℝ), 0 < κ →
      NoParallel (8*r+1) (arrangement r ε m δ κ) ∧
      NoConcurrent (8*r+1) (arrangement r ε m δ κ) ∧
      CrossingOrder r (arrangement r ε m δ κ) xDirection ∧
      TrianglePredicate (8*r+1) (arrangement r ε m δ κ) ⟨2*r-1,2*r,8*r⟩ ∧
      (0 < (intersection (arrangement r ε m δ κ (2*r-1))
        (arrangement r ε m δ κ (2*r))).2) ∧
      (∀ j, j < 8*r-1 → TrianglePredicate (8*r+1)
        (arrangement r ε m δ κ) (BBLNextSaturation.gapTriangle r j)) ∧
      ∃ us : List Triple, us.Nodup ∧
        (∀ t∈us, TrianglePredicate (8*r+1) (arrangement r ε m δ κ) t) ∧
        T+(4*r)^2 ≤ us.length := by
  let old := oldArrangement r ε m
  have h0 : old 0=graphLine 0 0 := by simp [old,oldArrangement]
  have hgraph : ∀ j < 4*r, old (j+1)=graphLine (m j) (oldIntercept r ε j) := by
    intro j _
    simp [old,oldArrangement]
  have hordered := old_intercepts_strict r hr ε hε0 hε
  have halt := BBLAlternation.saturated_alternation r (by omega) old hp hs m
    (oldIntercept r ε) h0 hgraph (fun j hj => hordered j (j+1) (by omega) hj)
    hsaturated hcenter
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
  have hct : TrianglePredicate (4*r+1) old ⟨0,2*r,2*r+1⟩ := by
    have hh := hsaturated (2*r-1) (by omega)
    simpa only [show 2*r-1+1=2*r by omega,
      show 2*r-1+2=2*r+1 by omega] using hh
  have hkeep := central_replaced_eventually r (by omega) old D hp hct
  have hall : ∀ᶠ κ in 𝓝 (0:ℝ), 0 < κ →
      NoParallel (8*r+1) (L κ) ∧ NoConcurrent (8*r+1) (L κ) ∧
      CrossingOrder r (L κ) xDirection ∧
      (∀ t∈ts, TrianglePredicate (8*r+1) (L κ) (replace r t)) ∧
      TrianglePredicate (8*r+1) (L κ) ⟨2*r-1,2*r,8*r⟩ := by
    filter_upwards [he,hret,hcentral,hkeep] with κ he hr hc hk
    intro hκ
    obtain ⟨hpn,hsn,ho⟩ := he (ne_of_gt hκ)
    refine ⟨hpn,hsn,ho,?_,?_⟩
    · simpa only [hrot] using hr hκ
    · simpa only [hrot] using hk (hc hκ)
  apply hall.mono
  intro κ hgood hκ
  obtain ⟨hpn,hsn,ho,hrt,hct'⟩ := hgood hκ
  have hcpos : 0 < (intersection (L κ (2*r-1)) (L κ (2*r))).2 := by
    rw [holdline κ (2*r-1) (by omega),holdline κ (2*r) (by omega)]
    simpa only [show 2*r-1+1=2*r by omega] using hcenter
  have hsats := BBLNextSaturation.next_saturated r (by omega) (L κ) xDirection
    hpn hsn (admissible_x r ε m δ κ) ho hct'
  obtain ⟨hrn,hrtri,hrc⟩ := replaced_witness r old (L κ) ts hn ht hrt
  obtain ⟨ms,hmn,hmt,hmc⟩ := mixed_witness r (by omega) (L κ) xDirection
    hpn hsn (admissible_x r ε m δ κ) ho
  let rs := ts.map (replace r)
  have hdisjoint : rs.Disjoint ms := by
    intro t ht hm
    have hlt := (hrtri t ht).2
    have hge := (hmt t hm).2
    omega
  refine ⟨hpn,hsn,ho,hct',hcpos,hsats,rs++ms,
    hrn.append hmn hdisjoint,?_,?_⟩
  · intro t ht
    rcases List.mem_append.mp ht with ht | ht
    · exact (hrtri t ht).1
    · exact (hmt t ht).1
  · dsimp [rs]
    rw [List.length_append,List.length_map]
    omega

#print axioms canonical_eventually
end Kobon.BBLRecursiveChoice
