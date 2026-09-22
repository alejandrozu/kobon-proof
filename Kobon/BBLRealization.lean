import Kobon.BBLCrossingCoordinates
import Kobon.BBLLiftedRows
import Kobon.BBLSimple

/-! Realization of the BBL integer crossing rows by the trigonometric pencil.
The perturbation δ fixes strict gaps; finite continuity then chooses κ.
No crossing order or triangle-count hypothesis is an input. -/
namespace Kobon.BBLRealization
open Real Exterior BBLExtrema BBLAnalytic BBLGrid BBLGridCuts BBLIntersection
  BBLPencilLimits BBLPencilRegularity BBLProfiles BBLLiftedKeys BBLCrossingCoordinates
  BBLRowOrder BBLRowGeometry BBLLiftedRows BBLSimple Filter
open scoped Topology
set_option maxHeartbeats 10000000

theorem horizontal_profile (r : Nat) (hr : 5≤r) (ε : ℝ) (i : Fin (4*r)) :
    Profile (8*(r:Int)) (cut r ε) (liftedNewKey (2*(r:Int)) i.val (4*(r:Int)))
      (newIntercept r i) := by
  have hi := i.isLt
  by_cases hil : i.val<2*r
  · have hkey : liftedNewKey (2*(r:Int)) i.val (4*(r:Int))=4*(i.val:Int) := by
      unfold liftedNewKey NegativeComplement newKey
      split_ifs <;> omega
    right; right; left
    refine ⟨2*(i.val:Int),by omega,by omega,by rw [hkey]; ring,?_⟩
    exact (cut_beta_left r hr ε i hil).symm
  · have hir : 2*r ≤ i.val := by omega
    have hkey : liftedNewKey (2*(r:Int)) i.val (4*(r:Int))=4*(i.val:Int)+4 := by
      unfold liftedNewKey NegativeComplement newKey
      split_ifs <;> omega
    right; right; left
    refine ⟨2*(i.val:Int)+2,by omega,by omega,by rw [hkey]; ring,?_⟩
    exact (cut_beta_right r hr ε i hir).symm

theorem old_profile (r : Nat) (ε : ℝ) (j : Fin (4*r)) :
    Profile (8*(r:Int)) (cut r ε) (oldKey j) (oldIntercept r ε j) := by
  right; right; left
  refine ⟨2*(j.val:Int)+1,by omega,by have := j.isLt; omega,?_,rfl⟩
  unfold oldKey
  ring

theorem coordinate_zero_profile (r : Nat) (hr : 5≤r) (ε : ℝ) (m : Nat → ℝ)
    (δ : ℝ) (hδ : GoodDelta r ε δ) (hm : ∀ j, j<4*r → m j≠0)
    (i : Fin (4*r)) (j : Fin (8*r+1)) (hij : j.val≠4*r+i.val) :
    Profile (8*(r:Int)) (cut r ε) (liftedCrossKey r i j)
      (rowCoordinate r ε m δ 0 i j) := by
  by_cases hj : j.val<4*r
  · rw [coordinate_old_zero r ε m δ i j hj (hm j hj)]
    simp only [liftedCrossKey,if_pos hj]
    exact old_profile r ε ⟨j.val,hj⟩
  by_cases hj0 : j.val=8*r
  · rw [hj0]
    simp only [liftedCrossKey,rowCoordinate,if_neg (show ¬8*r<4*r by omega),if_pos rfl]
    convert horizontal_profile r hr ε i using 1 <;> congr 1 <;> omega
  have hjnew : j.val-4*r<4*r := by omega
  let k : Fin (4*r) := ⟨j.val-4*r,hjnew⟩
  have hik : i≠k := by intro he; have := congrArg Fin.val he; dsimp [k] at this; omega
  have hh := (hδ.2 i k hik).2
  simp only [liftedCrossKey,rowCoordinate,if_neg hj,if_neg hj0]
  convert hh using 1 <;> try rfl
  congr 1
  dsimp [k]
  omega

theorem coordinate_order_eventually (r : Nat) (hr : 5≤r) (ε : ℝ)
    (hε0 : 0<ε) (hε : ε<tan (alpha r/2)) (m : Nat → ℝ)
    (δ : ℝ) (hδ : GoodDelta r ε δ) (hm : ∀ j, j<4*r → m j≠0) :
    ∀ᶠ κ in 𝓝 (0:ℝ), ∀ i : Fin (4*r), ∀ a b : Fin (8*r+1),
      a.val≠4*r+i.val → b.val≠4*r+i.val →
      liftedCrossKey r i a<liftedCrossKey r i b →
      rowCoordinate r ε m δ κ i a<rowCoordinate r ε m δ κ i b := by
  classical
  apply Filter.eventually_all.mpr
  intro i
  let S := {a : Fin (8*r+1) // a.val≠4*r+i.val}
  have he : ∀ᶠ κ in 𝓝 (0:ℝ), ∀ a b : S,
      liftedCrossKey r i a.val<liftedCrossKey r i b.val →
      rowCoordinate r ε m δ κ i a.val<rowCoordinate r ε m δ κ i b.val := by
    apply finite_order_persistence
    · intro a
      exact coordinate_continuous r ε m δ i a.val hm
    · intro a b hab
      exact profile_strict_order _ _ (by omega) (cut_increasing r hr ε hε0 hε) _ _ _ _
        (coordinate_zero_profile r hr ε m δ hδ hm i a.val a.property)
        (coordinate_zero_profile r hr ε m δ hδ hm i b.val b.property) hab
  exact he.mono (fun κ hh a b ha hb => hh ⟨a,ha⟩ ⟨b,hb⟩)

theorem strict_new_rows_eventually (r : Nat) (hr : 5≤r) (ε : ℝ)
    (hε0 : 0<ε) (hε : ε<tan (alpha r/2)) (m : Nat → ℝ)
    (δ : ℝ) (hδ : GoodDelta r ε δ) (hm : ∀ j, j<4*r → m j≠0) :
    ∀ᶠ κ in 𝓝 (0:ℝ), κ≠0 → ∀ i : Fin (4*r), ∀ a b : Fin (8*r+1),
      a.val≠4*r+i.val → b.val≠4*r+i.val →
      liftedCrossKey r i a<liftedCrossKey r i b →
      (intersection (arrangement r ε m δ κ (4*r+i)) (arrangement r ε m δ κ a)).1<
      (intersection (arrangement r ε m δ κ (4*r+i)) (arrangement r ε m δ κ b)).1 := by
  have ho := coordinate_order_eventually r hr ε hε0 hε m δ hδ hm
  have hs := old_slope_separation_eventually r m δ hm
  apply (ho.and hs).mono
  intro κ hκ hκ0 i a b ha hb hab
  have hm' : ∀ j, j<4*r → m j≠κ*slopeFactor δ (newIntercept r i) := by
    intro j hj
    exact hκ.2 i ⟨j,hj⟩
  rw [← coordinate_eq_crossing r hr ε m δ κ hδ hκ0 i a ha hm',
    ← coordinate_eq_crossing r hr ε m δ κ hδ hκ0 i b hb hm']
  exact hκ.1 i a b ha hb hab

noncomputable def horizontalCoordinate (r : Nat) (ε : ℝ) (j : Nat) : ℝ :=
  if j<4*r then oldIntercept r ε j else newIntercept r (j-4*r)

def xDirection : Line ℝ := ⟨1,0,0⟩

@[simp] theorem projection_xDirection (p : Point) : projection xDirection p=p.1 := by
  simp [projection,xDirection]

theorem horizontal_coordinate_profile (r : Nat) (hr : 5≤r) (ε : ℝ)
    (j : Fin (8*r+1)) (hj : j.val≠8*r) :
    Profile (8*(r:Int)) (cut r ε) (liftedCrossKey r (4*r) j)
      (horizontalCoordinate r ε j) := by
  by_cases hjo : j.val<4*r
  · simp only [horizontalCoordinate,liftedCrossKey,if_pos hjo]
    exact old_profile r ε ⟨j.val,hjo⟩
  let k : Fin (4*r) := ⟨j.val-4*r,by omega⟩
  have heq : liftedNewKey (2*(r:Int)) (4*(r:Int)) k.val=
      liftedNewKey (2*(r:Int)) k.val (4*(r:Int)) := by
    unfold liftedNewKey NegativeComplement newKey
    split_ifs <;> omega
  simp only [horizontalCoordinate,liftedCrossKey,if_neg hjo]
  convert horizontal_profile r hr ε k using 1
  · convert heq using 1 <;> congr 1 <;> dsimp [k] <;> omega

theorem horizontal_coordinate_eq (r : Nat) (hr : 5≤r) (ε : ℝ) (m : Nat → ℝ)
    (δ κ : ℝ) (hδ : GoodDelta r ε δ) (hκ : κ≠0)
    (hm : ∀ j, j<4*r → m j≠0) (j : Fin (8*r+1)) (hj : j.val≠8*r) :
    horizontalCoordinate r ε j=
      (intersection (arrangement r ε m δ κ (8*r)) (arrangement r ε m δ κ j)).1 := by
  rw [arrangement_zero,intersection_swap]
  by_cases hjo : j.val<4*r
  · rw [arrangement_old r ε m δ κ j hjo,
      BBLCapEnvelope.graph_horizontal_intersection _ _ (hm j hjo)]
    simp [horizontalCoordinate,hjo]
  let k : Fin (4*r) := ⟨j.val-4*r,by omega⟩
  have hjk : j.val=4*r+k.val := by dsimp [k]; omega
  rw [hjk,arrangement_new r ε m δ κ k k.isLt]
  unfold pencilLine
  rw [BBLCapEnvelope.graph_horizontal_intersection (κ*slopeFactor δ (newIntercept r k)) (newIntercept r k)
    (mul_ne_zero hκ (factor_ne _ _ hδ.1 (beta_tan_ne_zero r hr k)))]
  simp [horizontalCoordinate,show ¬4*r+k.val<4*r by omega]

theorem crossing_order_eventually (r : Nat) (hr : 5≤r) (ε : ℝ)
    (hε0 : 0<ε) (hε : ε<tan (alpha r/2)) (m : Nat → ℝ)
    (δ : ℝ) (hδ : GoodDelta r ε δ) (hm : ∀ j, j<4*r → m j≠0) :
    ∀ᶠ κ in 𝓝 (0:ℝ), κ≠0 → CrossingOrder r (arrangement r ε m δ κ) xDirection := by
  apply (strict_new_rows_eventually r hr ε hε0 hε m δ hδ hm).mono
  intro κ hrows hκ i hi a b ha hb hab
  simp only [projection_xDirection]
  have hle := (liftedCrossKey_le_iff r i (by omega) hi a b ha hb).mpr hab
  rcases lt_or_eq_of_le hle with hlt | heq
  · by_cases hiq : i<4*r
    · exact le_of_lt (hrows hκ ⟨i,hiq⟩ a b ha hb hlt)
    · have hieq : i=4*r := by omega
      subst i
      have ha' : a.val≠8*r := by omega
      have hb' : b.val≠8*r := by omega
      have hh := profile_strict_order _ _ (by omega) (cut_increasing r hr ε hε0 hε) _ _ _ _
        (horizontal_coordinate_profile r hr ε a ha')
        (horizontal_coordinate_profile r hr ε b hb') hlt
      rw [horizontal_coordinate_eq r hr ε m δ κ hδ hκ hm a ha',
        horizontal_coordinate_eq r hr ε m δ κ hδ hκ hm b hb'] at hh
      convert le_of_lt hh using 1 <;> congr 3 <;> omega
  · have he := liftedCrossKey_injective r i (by omega) hi a b ha hb heq
    rw [he]

theorem new_rows_injective_eventually (r : Nat) (hr : 5≤r) (ε : ℝ)
    (hε0 : 0<ε) (hε : ε<tan (alpha r/2)) (m : Nat → ℝ)
    (δ : ℝ) (hδ : GoodDelta r ε δ) (hm : ∀ j, j<4*r → m j≠0) :
    ∀ᶠ κ in 𝓝 (0:ℝ), κ≠0 → ∀ i : Fin (4*r),
      RowInjective (8*r+1) (arrangement r ε m δ κ) xDirection ⟨4*r+i,by have := i.isLt; omega⟩ := by
  apply (strict_new_rows_eventually r hr ε hε0 hε m δ hδ hm).mono
  intro κ hrows hκ i a b ha hb heq
  have ha' : a.val≠4*r+i.val := by intro h; apply ha; exact Fin.ext h
  have hb' : b.val≠4*r+i.val := by intro h; apply hb; exact Fin.ext h
  simp only [projection_xDirection] at heq
  apply liftedCrossKey_injective r i (by omega) (le_of_lt i.isLt) a b ha' hb'
  rcases lt_trichotomy (liftedCrossKey r i a) (liftedCrossKey r i b) with h | h | h
  · have hh := hrows hκ i a b ha' hb' h
    exact False.elim ((ne_of_lt hh) heq)
  · exact h
  · have hh := hrows hκ i b a hb' ha' h
    exact False.elim ((ne_of_lt hh) heq.symm)

#print axioms strict_new_rows_eventually
#print axioms crossing_order_eventually
#print axioms new_rows_injective_eventually
end Kobon.BBLRealization
