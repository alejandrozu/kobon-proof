import Kobon.BBLCentral
import Kobon.BBLRecursiveGrid

/-! The rightmost old line really acquires its last crossing at the central
auxiliary line. This joins the trigonometric strict maximum to affine geometry. -/
namespace Kobon.BBLRightmost
open Real Exterior BBLExtrema BBLAnalytic BBLGrid BBLGridCuts BBLIntersection
  BBLCentral BBLCrossingCoordinates BBLRealizedPencil BBLPencilRegularity Filter
open scoped Topology

theorem factor_sine (b δ : ℝ) (hb : cos b≠0) :
    slopeFactor δ (tan b)=sin (2*b)+δ/tan b := by
  unfold slopeFactor
  congr 1
  rw [tan_eq_sin_div_cos,sin_two_mul]
  have hs := sin_sq_add_cos_sq b
  have hd : 1+(sin b/cos b)^2≠0 := ne_of_gt (one_add_sq_pos _)
  field_simp [hb,hd]
  rw [show cos b^2+sin b^2=1 by linarith]
  ring

theorem old_right_intercept (r : Nat) (hr : 5≤r) (ε : ℝ) :
    oldIntercept r ε (4*r-1)=1/tan (alpha r) := by
  have hi : ((4*r-1:Nat):Int)=4*(r:Int)-1 := by omega
  unfold oldIntercept
  rw [hi,cut_right r ε _ (by omega)]
  have hid := (alpha_data r hr).2.2
  have he : rightAngle r (2*(4*(r:Int)-1)+1)=π/2-alpha r := by
    dsimp [rightAngle]
    push_cast
    nlinarith
  rw [he,tan_pi_div_two_sub]
  simp only [one_div]

theorem central_h_positive (r : Nat) (hr : 5≤r) (δ : ℝ) (hδ : 0<δ)
    (c : Fin (4*r)) (hc : c.val+1=3*r) : 0<h r c δ := by
  obtain ⟨ha,ha2,hid⟩ := alpha_data r hr
  have hb := beta_data r hr c
  have hcb : 0<beta r c := by
    have hcR : (c.val:ℝ)+1=3*(r:ℝ) := by exact_mod_cast hc
    dsimp [beta]
    nlinarith
  have hlt : beta r c<π/2-alpha r := by
    have hcR : (c.val:ℝ)+1=3*(r:ℝ) := by exact_mod_cast hc
    dsimp [beta]
    nlinarith
  have htan : tan (beta r c)<tan (π/2-alpha r) := by
    apply tan_lt_tan_of_lt_of_lt_pi_div_two (by linarith) (by linarith)
    exact hlt
  rw [tan_pi_div_two_sub] at htan
  have htpos := beta_tan_positive r hr c (by omega)
  have hf := factor_pos δ (tan (beta r c)) hδ htpos
  have hcne := ne_of_gt (beta_cos_pos r hr c)
  rw [factor_sine _ _ hcne] at hf
  exact mul_pos hf (sub_pos.mpr (by simpa only [one_div] using htan))

theorem pencil_max_eventually {n : Nat} (a m : ℝ) (s b : Fin n→ℝ)
    (c : Fin n) (hm : 0<m) (hc : 0<s c*(a-b c))
    (hmax : ∀ i : Fin n, i≠c → s i*(a-b i)<s c*(a-b c)) :
    ∀ᶠ κ in 𝓝 (0:ℝ), 0<κ →
      a < (intersection (graphLine m a) (graphLine (κ*s c) (b c))).1 ∧
      ∀ i : Fin n, i≠c →
        (intersection (graphLine m a) (graphLine (κ*s i) (b i))).1 <
          (intersection (graphLine m a) (graphLine (κ*s c) (b c))).1 := by
  let z := fun (i : Fin n) (κ : ℝ) => s i*(a-b i)/(m-κ*s i)
  have hcont (i : Fin n) : ContinuousAt (z i) 0 := by
    dsimp [z]
    fun_prop (disch := simp [ne_of_gt hm])
  have hpos : ∀ᶠ κ in 𝓝 (0:ℝ), 0<z c κ :=
    Filter.Tendsto.eventually_const_lt (by simpa [z] using div_pos hc hm) (hcont c)
  have hden : ∀ᶠ κ in 𝓝 (0:ℝ), ∀ i : Fin n, m-κ*s i≠0 := by
    apply Filter.eventually_all.mpr
    intro i
    have hh : ContinuousAt (fun κ : ℝ => m-κ*s i) 0 := by fun_prop
    exact hh.eventually_ne (by simpa using ne_of_gt hm)
  have horder : ∀ᶠ κ in 𝓝 (0:ℝ), ∀ i : Fin n, i≠c → z i κ<z c κ := by
    apply Filter.eventually_all.mpr
    intro i
    by_cases hi : i=c
    · exact Filter.Eventually.of_forall (fun _ hn => (hn hi).elim)
    have hh := (hcont i).eventually_lt (hcont c)
      (by simpa [z] using (div_lt_div_iff_of_pos_right hm).mpr (hmax i hi))
    exact hh.mono (fun _ h _ => h)
  filter_upwards [hpos,hden,horder] with κ hp hd ho
  intro hκ
  have hx (i : Fin n) :
      (intersection (graphLine m a) (graphLine (κ*s i) (b i))).1=a+κ*z i κ := by
    rw [graph_crossing_x _ _ _ _ (sub_ne_zero.mp (hd i))]
    dsimp [z]
    field_simp [hd i]
    ring
  rw [hx c]
  refine ⟨by nlinarith [mul_pos hκ hp],?_⟩
  intro i hi
  rw [hx i]
  nlinarith [mul_lt_mul_of_pos_left (ho i hi) hκ]

theorem central_pencil_eventually (r : Nat) (hr : 5≤r) (ε δ m : ℝ)
    (hδ : 0<δ) (hm : 0<m) (c : Fin (4*r)) (hc : c.val+1=3*r)
    (hmax : ∀ i : Fin (4*r), i≠c → h r i δ<h r c δ) :
    ∀ᶠ κ in 𝓝 (0:ℝ), 0<κ →
      oldIntercept r ε (4*r-1) <
        (intersection (graphLine m (oldIntercept r ε (4*r-1)))
          (pencilLine κ δ (newIntercept r c))).1 ∧
      ∀ i : Fin (4*r), i≠c →
        (intersection (graphLine m (oldIntercept r ε (4*r-1)))
          (pencilLine κ δ (newIntercept r i))).1 <
        (intersection (graphLine m (oldIntercept r ε (4*r-1)))
          (pencilLine κ δ (newIntercept r c))).1 := by
  have hh (i : Fin (4*r)) :
      slopeFactor δ (newIntercept r i)*(oldIntercept r ε (4*r-1)-newIntercept r i)=h r i δ := by
    rw [old_right_intercept r hr ε,newIntercept_fin,
      factor_sine _ _ (ne_of_gt (beta_cos_pos r hr i))]
    rfl
  exact pencil_max_eventually (oldIntercept r ε (4*r-1)) m
    (fun i : Fin (4*r) => slopeFactor δ (newIntercept r i)) (fun i => newIntercept r i)
    c hm (by rw [hh]; exact central_h_positive r hr δ hδ c hc)
    (fun i hi => by rw [hh,hh]; exact hmax i hi)

#print axioms central_pencil_eventually

theorem canonical_row_eventually (r : Nat) (hr : 5≤r) (ε δ : ℝ) (m : Nat→ℝ)
    (hδ : 0<δ) (hm : 0<m (4*r-1))
    (hmax : ∀ i : Fin (4*r), i.val≠3*r-1 →
      h r i δ<h r ⟨3*r-1,by omega⟩ δ)
    (hboundary : ∀ i : Fin (4*r+1), i.val≠4*r →
      (intersection (oldArrangement r ε m (4*r)) (oldArrangement r ε m i)).1
        ≤oldIntercept r ε (4*r-1)) :
    ∀ᶠ κ in 𝓝 (0:ℝ), 0<κ → ∀ i : Fin (8*r+1),
      i.val≠4*r-1 → i.val≠7*r-1 →
      (intersection (arrangement r ε m δ κ (4*r-1)) (arrangement r ε m δ κ i)).1 <
        (intersection (arrangement r ε m δ κ (4*r-1))
          (arrangement r ε m δ κ (7*r-1))).1 := by
  let c : Fin (4*r) := ⟨3*r-1,by omega⟩
  have he := central_pencil_eventually r hr ε δ (m (4*r-1)) hδ hm c (by dsimp [c]; omega)
    (fun i hi => hmax i (by intro hh; apply hi; apply Fin.ext; exact hh))
  apply he.mono
  intro κ hh hκ i hiR hiC
  obtain ⟨hb,hi⟩ := hh hκ
  have hR : arrangement r ε m δ κ (4*r-1)=
      graphLine (m (4*r-1)) (oldIntercept r ε (4*r-1)) :=
    arrangement_old r ε m δ κ (4*r-1) (by omega)
  have hC : arrangement r ε m δ κ (7*r-1)=pencilLine κ δ (newIntercept r c) := by
    have hid : 7*r-1=4*r+c.val := by dsimp [c]; omega
    rw [hid,arrangement_new r ε m δ κ c c.isLt]
  have hOldR : oldArrangement r ε m (4*r)=
      graphLine (m (4*r-1)) (oldIntercept r ε (4*r-1)) := by
    simp only [oldArrangement,show 4*r≠0 by omega,if_false]
  rw [hR,hC]
  by_cases hio : i.val<4*r
  · have hbi := hboundary ⟨i.val+1,by omega⟩ (by change i.val+1≠4*r; omega)
    rw [hOldR] at hbi
    have hil : oldArrangement r ε m (i.val+1)=arrangement r ε m δ κ i := by
      simp only [oldArrangement,Nat.add_eq_zero_iff,one_ne_zero,and_false,if_false,
        Nat.add_sub_cancel,arrangement_old r ε m δ κ i hio]
    rw [hil] at hbi
    exact lt_of_le_of_lt hbi hb
  by_cases hin : i.val<8*r
  · let k : Fin (4*r) := ⟨i.val-4*r,by omega⟩
    have hik : i.val=4*r+k.val := by dsimp [k]; omega
    have hkc : k≠c := by intro h; have hh := congrArg Fin.val h; dsimp [k,c] at hh; omega
    rw [hik,arrangement_new r ε m δ κ k k.isLt]
    exact hi k hkc
  · have hiz : i.val=8*r := by omega
    rw [hiz,arrangement_zero]
    have hb0 := hboundary ⟨0,by omega⟩ (by change 0≠4*r; omega)
    rw [hOldR] at hb0
    simpa [oldArrangement] using lt_of_le_of_lt hb0 hb

#print axioms canonical_row_eventually
end Kobon.BBLRightmost
