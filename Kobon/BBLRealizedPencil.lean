import Kobon.BBLRealization
import Kobon.BBLRegularity

/-! A genuine all-size real-line BBL pencil, with simplicity and actual
mixed triangles. Old-triangle retention and iteration are separate results. -/
namespace Kobon.BBLRealizedPencil
open Real Exterior BBLExtrema BBLAnalytic BBLGrid BBLGridCuts BBLIntersection
  BBLPencilRegularity BBLCrossingCoordinates BBLRealization BBLRowGeometry
  BBLSimple Filter
open scoped Topology

noncomputable def oldArrangement (r : Nat) (ε : ℝ) (m : Nat → ℝ) (j : Nat) : Line ℝ :=
  if j=0 then graphLine 0 0 else graphLine (m (j-1)) (oldIntercept r ε (j-1))

theorem arrangement_eq_canonical (r : Nat) (ε : ℝ) (m : Nat → ℝ) (δ κ : ℝ) :
    arrangement r ε m δ κ=BBLRegularity.canonical (4*r) m (oldIntercept r ε)
      (fun i => slopeFactor δ (newIntercept r i)) (newIntercept r) κ := by
  funext j
  simp only [arrangement,BBLRegularity.canonical,pencilLine,show 2*(4*r)=8*r by omega]

theorem no_parallel_eventually (r : Nat) (hr : 5≤r) (ε : ℝ) (m : Nat → ℝ)
    (δ : ℝ) (hδ : GoodDelta r ε δ) (hm : ∀ j, j<4*r → m j≠0)
    (hmij : ∀ i j : Fin (4*r), i<j → m i≠m j) :
    ∀ᶠ κ in 𝓝 (0:ℝ), κ≠0 → NoParallel (8*r+1) (arrangement r ε m δ κ) := by
  have hv : ∀ i : Fin (4*r), slopeFactor δ (newIntercept r i)≠0 := by
    intro i
    exact factor_ne _ _ hδ.1 (beta_tan_ne_zero r hr i)
  have hvij : ∀ i j : Fin (4*r), i<j →
      slopeFactor δ (newIntercept r i)≠slopeFactor δ (newIntercept r j) := by
    intro i j hij
    exact factors_distinct _ _ _ (beta_tan_ne_zero r hr i) (beta_tan_ne_zero r hr j)
      ((beta_tan_strictMono r hr).injective.ne (ne_of_lt hij)) (hδ.2 i j (ne_of_lt hij)).1
  have hh := BBLRegularity.canonical_no_parallel_eventually (4*r) m (oldIntercept r ε)
    (fun i => slopeFactor δ (newIntercept r i)) (newIntercept r)
    (fun i => hm i i.isLt) hv hmij hvij
  simpa only [← arrangement_eq_canonical,show 2*(4*r)=8*r by omega] using hh

theorem admissible_x (r : Nat) (ε : ℝ) (m : Nat → ℝ) (δ κ : ℝ) :
    Admissible (8*r+1) (arrangement r ε m δ κ) xDirection := by
  intro i
  unfold arrangement
  split_ifs <;> norm_num [det,graphLine,pencilLine,xDirection]

theorem no_concurrent (r : Nat) (ε : ℝ) (m : Nat → ℝ) (δ κ : ℝ)
    (hp : NoParallel (8*r+1) (arrangement r ε m δ κ))
    (hs : NoConcurrent (4*r+1) (oldArrangement r ε m))
    (hrows : ∀ i : Fin (4*r), RowInjective (8*r+1) (arrangement r ε m δ κ)
      xDirection ⟨4*r+i,by have := i.isLt; omega⟩) :
    NoConcurrent (8*r+1) (arrangement r ε m δ κ) := by
  have hn : 2*(4*r)=8*r := by omega
  rw [← hn]
  apply canonical_no_concurrent (4*r) (arrangement r ε m δ κ) (oldArrangement r ε m) xDirection
    (by simpa only [hn] using hp) hs
  · intro j hj
    rw [arrangement_old r ε m δ κ j hj]
    simp [oldArrangement]
  · rw [hn,arrangement_zero]
    simp [oldArrangement]
  · intro j hj hj'
    let i : Fin (4*r) := ⟨j.val-4*r,by omega⟩
    have hindex : 4*r+i.val=j.val := by dsimp [i]; omega
    intro a b ha hb heq
    have ha' : (⟨a.val,by omega⟩ : Fin (8*r+1))≠⟨4*r+i.val,by have := i.isLt; omega⟩ := by
      intro he
      apply ha
      apply Fin.ext
      simpa only [hindex] using congrArg Fin.val he
    have hb' : (⟨b.val,by omega⟩ : Fin (8*r+1))≠⟨4*r+i.val,by have := i.isLt; omega⟩ := by
      intro he
      apply hb
      apply Fin.ext
      simpa only [hindex] using congrArg Fin.val he
    have hh := hrows i ⟨a.val,by omega⟩ ⟨b.val,by omega⟩ ha' hb'
      (by simpa only [hindex] using heq)
    apply Fin.ext
    have hv : a.val=b.val := congrArg (fun z : Fin (8*r+1) => z.val) hh
    exact hv

/-- All sufficiently small nonzero scales realize the simple crossing model.
The eventual form lets cap and old-triangle persistence be imposed together. -/
theorem realized_pencil_eventually (r : Nat) (hr : 5≤r) (ε : ℝ)
    (hε0 : 0<ε) (hε : ε<tan (alpha r/2)) (m : Nat → ℝ)
    (δ : ℝ) (hδ : GoodDelta r ε δ)
    (hm : ∀ j, j<4*r → m j≠0)
    (hmij : ∀ i j : Fin (4*r), i<j → m i≠m j)
    (hs : NoConcurrent (4*r+1) (oldArrangement r ε m)) :
    ∀ᶠ κ in 𝓝 (0:ℝ), κ≠0 →
      NoParallel (8*r+1) (arrangement r ε m δ κ) ∧
      NoConcurrent (8*r+1) (arrangement r ε m δ κ) ∧
      CrossingOrder r (arrangement r ε m δ κ) xDirection := by
  have hp := no_parallel_eventually r hr ε m δ hδ hm hmij
  have ho := crossing_order_eventually r hr ε hε0 hε m δ hδ hm
  have hi := new_rows_injective_eventually r hr ε hε0 hε m δ hδ hm
  exact (hp.and (ho.and hi)).mono (fun κ h hκ =>
    ⟨h.1 hκ,no_concurrent r ε m δ κ (h.1 hκ) hs (h.2.2 hκ),h.2.1 hκ⟩)

/-- For every prescribed tangent grid and every simple old graph arrangement
on it, there is a simple real pencil realizing all integer rows and producing
at least q² actual mixed triangles. This is a geometric existence theorem. -/
theorem realized_pencil_exists (r : Nat) (hr : 5≤r) (ε : ℝ)
    (hε0 : 0<ε) (hε : ε<tan (alpha r/2)) (m : Nat → ℝ)
    (hm : ∀ j, j<4*r → m j≠0)
    (hmij : ∀ i j : Fin (4*r), i<j → m i≠m j)
    (hs : NoConcurrent (4*r+1) (oldArrangement r ε m)) :
    ∃ δ κ : ℝ, 0<δ ∧ 0<κ ∧
      NoParallel (8*r+1) (arrangement r ε m δ κ) ∧
      NoConcurrent (8*r+1) (arrangement r ε m δ κ) ∧
      CrossingOrder r (arrangement r ε m δ κ) xDirection ∧
      ∃ ts : List Triple, ts.Nodup ∧
        (∀ t∈ts, TrianglePredicate (8*r+1) (arrangement r ε m δ κ) t ∧ 4*r≤t.j) ∧
        (4*r)^2≤ts.length := by
  obtain ⟨δ,hδ⟩ := good_delta_exists r hr ε hε0 hε
  have he := realized_pencil_eventually r hr ε hε0 hε m δ hδ hm hmij hs
  obtain ⟨κ,hκ,hgood⟩ := positive_eventually_exists _
    (he.mono (fun κ h hκ => h (ne_of_gt hκ)))
  exact ⟨δ,κ,hδ.1,hκ,hgood.1,hgood.2.1,hgood.2.2,
    mixed_witness r (by omega) _ xDirection hgood.1 hgood.2.1
      (admissible_x r ε m δ κ) hgood.2.2⟩

#print axioms realized_pencil_exists
end Kobon.BBLRealizedPencil
