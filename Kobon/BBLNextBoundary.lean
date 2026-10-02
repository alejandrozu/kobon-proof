import Kobon.BBLProjection
import Kobon.BBLVisible
import Kobon.BBLRecursiveGrid

/-! The new rightmost line automatically has a clean rightward ray.
The projection and admissibility conditions persist at small pencil scale. -/
namespace Kobon.BBLNextBoundary
open Real Exterior BBLExtrema BBLAnalytic BBLIntersection BBLPencilRegularity
  BBLCrossingCoordinates BBLRealization BBLRealizedPencil BBLCanonicalPencil
  BBLRowGeometry BBLVisible BBLProjection Filter
open scoped Topology

noncomputable def auxSlope (r : Nat) (δ κ : ℝ) (i : Nat) : ℝ :=
  if i<4*r then κ*slopeFactor δ (newIntercept r i) else 0
noncomputable def auxIntercept (r i : Nat) : ℝ :=
  if i<4*r then newIntercept r i else 0

theorem aux_graph (r : Nat) (ε : ℝ) (m : Nat→ℝ) (δ κ : ℝ)
    (i : Nat) (hi : i≤4*r) :
    arrangement r ε m δ κ (4*r+i)=graphLine (auxSlope r δ κ i) (auxIntercept r i) := by
  by_cases h : i<4*r
  · simp only [auxSlope,auxIntercept,h,if_pos,arrangement_new r ε m δ κ i h,pencilLine]
  · have he : i=4*r := by omega
    subst i
    simp only [auxSlope,auxIntercept,lt_self_iff_false,if_false,
      show 4*r+4*r=8*r by omega,arrangement_zero]

theorem positive_directions_eventually (r : Nat) (δ : ℝ) (w : Line ℝ) (hw : 0<w.a) :
    ∀ᶠ κ in 𝓝 (0:ℝ), ∀ i, i≤4*r → 0<w.a+w.b*auxSlope r δ κ i := by
  have hall : ∀ᶠ κ in 𝓝 (0:ℝ), ∀ i : Fin (4*r+1), 0<w.a+w.b*auxSlope r δ κ i := by
    apply Filter.eventually_all.mpr
    intro i
    have hf : ContinuousAt (fun κ : ℝ => w.a+w.b*auxSlope r δ κ i) 0 := by
      unfold auxSlope
      split_ifs <;> fun_prop
    apply Filter.Tendsto.eventually_const_lt _ hf
    simpa [auxSlope] using hw
  exact hall.mono (fun _ h i hi => h ⟨i,by omega⟩)

theorem admissible_of_directions (r : Nat) (ε : ℝ) (m : Nat→ℝ) (δ κ : ℝ) (w : Line ℝ)
    (hold : Admissible (4*r+1) (oldArrangement r ε m) w)
    (hpos : ∀ i, i≤4*r → 0<w.a+w.b*auxSlope r δ κ i) :
    Admissible (8*r+1) (arrangement r ε m δ κ) w := by
  intro i
  by_cases hi : i.val<4*r
  · have hh := hold ⟨i.val+1,by omega⟩
    simpa only [oldArrangement,Nat.add_eq_zero_iff,one_ne_zero,and_false,if_false,
      Nat.add_sub_cancel,arrangement_old r ε m δ κ i hi] using hh
  · have hb : i.val-4*r≤4*r := by omega
    have he : i.val=4*r+(i.val-4*r) := by omega
    rw [he,aux_graph r ε m δ κ _ hb]
    have hh := hpos (i.val-4*r) hb
    dsimp [det,graphLine]
    nlinarith

theorem crossing_order_oblique (r : Nat) (ε : ℝ) (m : Nat→ℝ) (δ κ : ℝ) (w : Line ℝ)
    (hp : NoParallel (8*r+1) (arrangement r ε m δ κ))
    (hpos : ∀ i, i≤4*r → 0<w.a+w.b*auxSlope r δ κ i)
    (ho : CrossingOrder r (arrangement r ε m δ κ) xDirection) :
    CrossingOrder r (arrangement r ε m δ κ) w :=
  crossing_order_transfer r _ w hp (auxSlope r δ κ) (auxIntercept r)
    (aux_graph r ε m δ κ) (fun i hi => le_of_lt (hpos i hi)) ho

theorem graph_zero_intersection_x (m a : ℝ) (hm : m≠0) :
    (intersection (graphLine m a) (graphLine 0 0)).1=a := by
  rw [graph_crossing_x m a 0 0 hm]
  simp [hm]

theorem next_rightmost_boundary (r : Nat) (hr : 5≤r) (ε : ℝ) (m : Nat→ℝ) (δ κ : ℝ)
    (hδ : 0<δ) (hκ : 0<κ)
    (hp : NoParallel (8*r+1) (arrangement r ε m δ κ))
    (hs : NoConcurrent (8*r+1) (arrangement r ε m δ κ))
    (ho : CrossingOrder r (arrangement r ε m δ κ) xDirection) :
    ∀ i : Fin (8*r+1), i.val≠8*r-1 →
      (intersection (arrangement r ε m δ κ (8*r-1)) (arrangement r ε m δ κ i)).1
        ≤newIntercept r (4*r-1) := by
  let L := arrangement r ε m δ κ
  have hv := aux_visible r (2*r-1) (by omega) (by omega) L xDirection hp hs
    (admissible_x r ε m δ κ) ho
  have ht : auxVisible r (2*r-1)=⟨8*r-1,8*r,8*r+1⟩ := by
    unfold auxVisible auxPair
    rw [if_neg (by omega),if_neg (by omega)]
    congr 1 <;> omega
  rw [ht] at hv
  have hlast : L (8*r-1)=pencilLine κ δ (newIntercept r (4*r-1)) := by
    have hid : 8*r-1=4*r+(4*r-1) := by omega
    exact hid ▸ arrangement_new r ε m δ κ (4*r-1) (by omega)
  have hzero : L (8*r)=graphLine 0 0 := arrangement_zero r ε m δ κ
  have hms := new_slopes_pos r hr δ κ hδ hκ (4*r-1) (by omega) (by omega)
  have hx : (intersection (L (8*r-1)) (L (8*r))).1=newIntercept r (4*r-1) := by
    rw [hlast,hzero,pencilLine,graph_zero_intersection_x _ _ (ne_of_gt hms)]
  intro i hi
  have hh := visible_extremal (8*r+1) L xDirection hp (admissible_x r ε m δ κ)
    ⟨8*r-1,8*r,8*r+1⟩ hv i hi
  simpa only [projection,xDirection,one_mul,zero_mul,add_zero,hx] using hh

#print axioms next_rightmost_boundary
end Kobon.BBLNextBoundary
