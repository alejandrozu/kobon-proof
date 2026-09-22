import Kobon.BBLPencilRegularity
import Kobon.BBLCapEnvelope

/-! Continuous extensions of the crossing coordinates at pencil scale zero.
New-new coordinates are constant in the scale. Old-new coordinates converge
to the prescribed old intercepts. Every equality below concerns real lines. -/
namespace Kobon.BBLCrossingCoordinates
open Real Exterior BBLExtrema BBLAnalytic BBLGrid BBLGridCuts BBLIntersection
  BBLPencilLimits BBLPencilProfiles BBLPencilRegularity BBLProfiles BBLLiftedKeys Filter
open scoped Topology

noncomputable def oldIntercept (r : Nat) (ε : ℝ) (j : Nat) : ℝ :=
  cut r ε (2*(j:Int)+1)
noncomputable def newIntercept (r i : Nat) : ℝ :=
  tan (-π/2+((i:ℝ)+1/2)*alpha r)

theorem newIntercept_fin (r : Nat) (i : Fin (4*r)) :
    newIntercept r i = tan (beta r i) := rfl

noncomputable def arrangement (r : Nat) (ε : ℝ) (m : Nat → ℝ)
    (δ κ : ℝ) (j : Nat) : Line ℝ :=
  if j<4*r then graphLine (m j) (oldIntercept r ε j)
  else if j<8*r then pencilLine κ δ (newIntercept r (j-4*r))
  else graphLine 0 0

noncomputable def rowCoordinate (r : Nat) (ε : ℝ) (m : Nat → ℝ)
    (δ κ : ℝ) (i j : Nat) : ℝ :=
  if j<4*r then
    (m j*oldIntercept r ε j-κ*slopeFactor δ (newIntercept r i)*newIntercept r i)/
      (m j-κ*slopeFactor δ (newIntercept r i))
  else if j=8*r then newIntercept r i
  else pairX δ (newIntercept r i) (newIntercept r (j-4*r))

theorem arrangement_old (r : Nat) (ε : ℝ) (m : Nat → ℝ) (δ κ : ℝ)
    (j : Nat) (hj : j<4*r) :
    arrangement r ε m δ κ j=graphLine (m j) (oldIntercept r ε j) := by
  simp [arrangement,hj]

theorem arrangement_new (r : Nat) (ε : ℝ) (m : Nat → ℝ) (δ κ : ℝ)
    (i : Nat) (hi : i<4*r) :
    arrangement r ε m δ κ (4*r+i)=pencilLine κ δ (newIntercept r i) := by
  simp [arrangement,show ¬4*r+i<4*r by omega,show 4*r+i<8*r by omega]

theorem arrangement_zero (r : Nat) (ε : ℝ) (m : Nat → ℝ) (δ κ : ℝ) :
    arrangement r ε m δ κ (8*r)=graphLine 0 0 := by
  simp [arrangement,show ¬8*r<4*r by omega]

theorem coordinate_old_zero (r : Nat) (ε : ℝ) (m : Nat → ℝ) (δ : ℝ)
    (i j : Nat) (hj : j<4*r) (hm : m j≠0) :
    rowCoordinate r ε m δ 0 i j=oldIntercept r ε j := by
  simp [rowCoordinate,hj,hm]

theorem coordinate_continuous (r : Nat) (ε : ℝ) (m : Nat → ℝ) (δ : ℝ)
    (i j : Nat) (hm : ∀ j, j<4*r → m j≠0) :
    ContinuousAt (fun κ => rowCoordinate r ε m δ κ i j) 0 := by
  unfold rowCoordinate
  split_ifs with hj
  · fun_prop (disch := simpa using hm j hj)
  · exact continuousAt_const
  · exact continuousAt_const

theorem coordinate_eq_crossing (r : Nat) (hr : 5≤r) (ε : ℝ) (m : Nat → ℝ)
    (δ κ : ℝ) (hδ : GoodDelta r ε δ) (hκ : κ≠0)
    (i : Fin (4*r)) (j : Fin (8*r+1)) (hij : j.val≠4*r+i.val)
    (hm : ∀ j, j<4*r → m j≠κ*slopeFactor δ (newIntercept r i)) :
    rowCoordinate r ε m δ κ i j=
      (intersection (arrangement r ε m δ κ (4*r+i)) (arrangement r ε m δ κ j)).1 := by
  rw [arrangement_new r ε m δ κ i i.isLt]
  by_cases hj : j.val<4*r
  · rw [arrangement_old r ε m δ κ j hj,intersection_swap]
    simp only [rowCoordinate,if_pos hj]
    exact (graph_crossing_x _ _ _ _ (hm j hj)).symm
  by_cases hj0 : j.val=8*r
  · rw [hj0,arrangement_zero]
    simp only [rowCoordinate,if_neg (show ¬8*r<4*r by omega),if_pos rfl]
    unfold pencilLine
    rw [BBLCapEnvelope.graph_horizontal_intersection]
    · rfl
    · exact mul_ne_zero hκ (factor_ne _ _ hδ.1 (beta_tan_ne_zero r hr i))
  have hjnew : j.val-4*r<4*r := by omega
  let k : Fin (4*r) := ⟨j.val-4*r,hjnew⟩
  have hjk : j.val=4*r+k.val := by dsimp [k]; omega
  have hik : i≠k := by intro he; apply hij; rw [he,hjk]
  have hpair := hδ.2 i k hik
  rw [hjk,arrangement_new r ε m δ κ k k.isLt]
  simp only [rowCoordinate,if_neg (show ¬4*r+k.val<4*r by omega),
    if_neg (show 4*r+k.val≠8*r by omega),Nat.add_sub_cancel_left]
  exact (pencil_crossing_x κ δ _ _ hκ (beta_tan_ne_zero r hr i)
    (beta_tan_ne_zero r hr k) ((beta_tan_strictMono r hr).injective.ne hik) hpair.1).symm

theorem old_slope_separation_eventually (r : Nat) (m : Nat → ℝ) (δ : ℝ)
    (hm : ∀ j, j<4*r → m j≠0) :
    ∀ᶠ κ in 𝓝 (0:ℝ), ∀ i j : Fin (4*r), m j≠κ*slopeFactor δ (newIntercept r i) := by
  apply Filter.eventually_all.mpr
  intro i
  apply Filter.eventually_all.mpr
  intro j
  have hc : ContinuousAt (fun κ : ℝ => m j-κ*slopeFactor δ (newIntercept r i)) 0 := by fun_prop
  exact (hc.eventually_ne (by simpa using hm j j.isLt)).mono
    (fun _ hh => sub_ne_zero.mp hh)

#print axioms coordinate_eq_crossing
#print axioms old_slope_separation_eventually
end Kobon.BBLCrossingCoordinates
