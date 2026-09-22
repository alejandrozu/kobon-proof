import Kobon.FurediPalastiChart

/-! Convex-hull exposure for the classical half-phase construction.

The lemmas in this module are geometric/trigonometric ingredients for changing
the affine chart. They do not themselves assert a new lower-bound theorem.
-/
namespace Kobon.FurediPalastiCaps

open Kobon.FurediPalasti

noncomputable def pairX (u v : ℝ) : ℝ :=
  2 * Real.cos (u+v) * Real.cos (u-v) + 2 * Real.cos (u+v)^2 - 1

theorem quadratic_nonadjacent {c z w : ℝ}
    (hc0 : 3/4 ≤ c) (hc1 : c < 1)
    (hw : |w| ≤ 2*c^2-1) :
    -(1+2*c)/2 < 2*z*w+2*z^2-1 := by
  have hp : 0 < 2*c^3+2*c^2-1 := by
    have h1 : 0 ≤ (c-3/4)^2 := sq_nonneg _
    have h2 : 0 ≤ (c-3/4)^2*(c+3/2) := mul_nonneg h1 (by linarith)
    nlinarith
  have hprod : 0 < (1-c)*(2*c^3+2*c^2-1) :=
    mul_pos (by linarith) hp
  have hc : 0 ≤ 2*c^2-1 := le_trans (abs_nonneg _) hw
  have hw2 : w^2 ≤ (2*c^2-1)^2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg w) hc).mpr hw
  nlinarith [sq_nonneg (z+w/2)]

theorem quadratic_adjacent {c z : ℝ}
    (hc1 : c < 1) (hz : z ≤ -(1/2) ∨ 1/2-c < z) :
    -(1+2*c)/2 ≤ 2*z*c+2*z^2-1 := by
  rcases hz with hz | hz
  · have : 0 ≤ (2*z+1)*(z+c-1/2) :=
      mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)
    nlinarith
  · have : 0 < (2*z+1)*(z+c-1/2) := mul_pos (by linarith) (by linarith)
    nlinarith

theorem quadratic_adjacent_strict {c z : ℝ}
    (hc1 : c < 1) (hz : z < -(1/2) ∨ 1/2-c < z) :
    -(1+2*c)/2 < 2*z*c+2*z^2-1 := by
  rcases hz with hz | hz
  · have : 0 < (2*z+1)*(z+c-1/2) :=
      mul_pos_of_neg_of_neg (by linarith) (by linarith)
    nlinarith
  · have : 0 < (2*z+1)*(z+c-1/2) := mul_pos (by linarith) (by linarith)
    nlinarith

theorem cos_two_thirds_pi : Real.cos (2*Real.pi/3) = -(1/2) := by
  rw [show 2*Real.pi/3 = Real.pi-Real.pi/3 by ring, Real.cos_pi_sub,
    Real.cos_pi_div_three]

theorem cos_four_thirds_pi : Real.cos (4*Real.pi/3) = -(1/2) := by
  rw [show 4*Real.pi/3 = 2*Real.pi-(2*Real.pi/3) by ring,
    Real.cos_two_pi_sub, cos_two_thirds_pi]

theorem cos_near_two_thirds {a : ℝ} (ha : 0 < a) (ha' : a ≤ Real.pi/6) :
    1/2-Real.cos a < Real.cos (2*Real.pi/3-2*a) := by
  have hc0 : 0 < Real.cos a := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have hc1 : Real.cos a < 1 := by
    simpa using Real.cos_lt_cos_of_nonneg_of_le_pi (x:=0) (y:=a) (by norm_num)
      (by linarith [Real.pi_pos]) ha
  have hs : 0 ≤ Real.sin a := Real.sin_nonneg_of_nonneg_of_le_pi (le_of_lt ha) (by linarith [Real.pi_pos])
  have hS : 0 ≤ Real.sin (2*Real.pi/3) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by positivity) (by linarith [Real.pi_pos])
  rw [Real.cos_sub, cos_two_thirds_pi, Real.cos_two_mul, Real.sin_two_mul]
  have hp : 0 < Real.cos a * (1-Real.cos a) := mul_pos hc0 (by linarith)
  have hq : 0 ≤ Real.sin (2*Real.pi/3) * (2*Real.sin a*Real.cos a) :=
    mul_nonneg hS (by positivity)
  nlinarith

theorem cos_central_band {x : ℝ}
    (hlo : 2*Real.pi/3 ≤ x) (hhi : x ≤ 4*Real.pi/3) :
    Real.cos x ≤ -(1/2) := by
  by_cases hx : x ≤ Real.pi
  · calc
      Real.cos x ≤ Real.cos (2*Real.pi/3) :=
        Real.cos_le_cos_of_nonneg_of_le_pi (by positivity) hx hlo
      _ = -(1/2) := cos_two_thirds_pi
  · rw [← Real.cos_two_pi_sub x]
    calc
      Real.cos (2*Real.pi-x) ≤ Real.cos (2*Real.pi/3) :=
        Real.cos_le_cos_of_nonneg_of_le_pi (by positivity) (by linarith) (by linarith)
      _ = -(1/2) := cos_two_thirds_pi

theorem cos_central_band_strict {x : ℝ}
    (hlo : 2*Real.pi/3 < x) (hhi : x < 4*Real.pi/3) :
    Real.cos x < -(1/2) := by
  by_cases hx : x ≤ Real.pi
  · calc
      Real.cos x < Real.cos (2*Real.pi/3) :=
        Real.cos_lt_cos_of_nonneg_of_le_pi (by positivity) hx hlo
      _ = -(1/2) := cos_two_thirds_pi
  · rw [← Real.cos_two_pi_sub x]
    calc
      Real.cos (2*Real.pi-x) < Real.cos (2*Real.pi/3) :=
        Real.cos_lt_cos_of_nonneg_of_le_pi (by positivity) (by linarith) (by linarith)
      _ = -(1/2) := cos_two_thirds_pi

theorem cos_outer_bands {a x : ℝ} (ha : 0 < a) (ha' : a ≤ Real.pi/6)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 2*Real.pi)
    (hx : x ≤ 2*Real.pi/3-2*a ∨ 4*Real.pi/3+2*a ≤ x) :
    1/2-Real.cos a < Real.cos x := by
  have hnear := cos_near_two_thirds ha ha'
  rcases hx with hx | hx
  · exact lt_of_lt_of_le hnear
      (Real.cos_le_cos_of_nonneg_of_le_pi hx0 (by linarith [Real.pi_pos]) hx)
  · rw [← Real.cos_two_pi_sub x]
    exact lt_of_lt_of_le hnear
      (Real.cos_le_cos_of_nonneg_of_le_pi (by linarith) (by linarith [Real.pi_pos]) (by linarith))

theorem abs_cos_middle {a x : ℝ} (ha : 0 ≤ a) (ha' : a ≤ Real.pi/4)
    (hlo : 2*a ≤ x) (hhi : x ≤ Real.pi-2*a) :
    |Real.cos x| ≤ Real.cos (2*a) := by
  apply abs_le.mpr
  constructor
  · have h := Real.cos_le_cos_of_nonneg_of_le_pi (x:=x) (y:=Real.pi-2*a)
      (by linarith) (by linarith) hhi
    rw [Real.cos_pi_sub] at h
    linarith
  · exact Real.cos_le_cos_of_nonneg_of_le_pi (by linarith) (by linarith) hlo

noncomputable def step (n : ℕ) : ℝ := Real.pi/(n:ℝ)

theorem step_bounds {n : ℕ} (hn : 6 ≤ n) :
    0 < step n ∧ step n ≤ Real.pi/6 := by
  have hnR : (6:ℝ) ≤ n := by exact_mod_cast hn
  constructor
  · unfold step; positivity
  · unfold step
    apply (div_le_iff₀ (by linarith : (0:ℝ)<n)).mpr
    nlinarith [Real.pi_pos]

theorem cos_step_bounds {n : ℕ} (hn : 6 ≤ n) :
    3/4 ≤ Real.cos (step n) ∧ Real.cos (step n) < 1 := by
  have ha := step_bounds hn
  have h := Real.cos_le_cos_of_nonneg_of_le_pi (le_of_lt ha.1)
    (show Real.pi/6 ≤ Real.pi by linarith [Real.pi_pos]) ha.2
  rw [Real.cos_pi_div_six] at h
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num)
  have hs0 := Real.sqrt_nonneg (3:ℝ)
  have hS : (3:ℝ)/4 ≤ Real.sqrt 3/2 := by nlinarith
  constructor
  · linarith
  · simpa using Real.cos_lt_cos_of_nonneg_of_le_pi (x:=0) (y:=step n)
      (by norm_num) (by linarith [Real.pi_pos]) ha.1

theorem angle_eq_step (n i : ℕ) : angle n i = ((i:ℝ)+1/2)*step n := by
  simp only [angle,step]
  ring

theorem step_mul {n : ℕ} (hn : 0 < n) : (n:ℝ)*step n = Real.pi := by
  unfold step
  have : (n:ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  field_simp

theorem adjacent_cos_strict {m k : ℕ} (hm : 2 ≤ m) (hk : k < 3*m)
    (hkm : k ≠ m) (hk2m : k ≠ 2*m) :
    Real.cos (2*(k:ℝ)*step (3*m)) < -(1/2) ∨
      1/2-Real.cos (step (3*m)) < Real.cos (2*(k:ℝ)*step (3*m)) := by
  have ha := step_bounds (show 6 ≤ 3*m by omega)
  have hpi := step_mul (show 0 < 3*m by omega)
  push_cast at hpi
  have hk0 : (0:ℝ) ≤ k := Nat.cast_nonneg _
  have hkR : (k:ℝ) < 3*(m:ℝ) := by exact_mod_cast hk
  by_cases hlow : k < m
  · right
    have hR : (k:ℝ)+1 ≤ m := by exact_mod_cast hlow
    have hmul := mul_le_mul_of_nonneg_right hR (le_of_lt ha.1)
    apply cos_outer_bands ha.1 ha.2
    · exact mul_nonneg (mul_nonneg (by norm_num) hk0) ha.1.le
    · nlinarith
    · left; nlinarith
  by_cases hhigh : 2*m < k
  · right
    have hR : 2*(m:ℝ)+1 ≤ k := by exact_mod_cast hhigh
    have hmul := mul_le_mul_of_nonneg_right hR (le_of_lt ha.1)
    apply cos_outer_bands ha.1 ha.2
    · exact mul_nonneg (mul_nonneg (by norm_num) hk0) ha.1.le
    · nlinarith
    · right; nlinarith
  · left
    have hR1 : (m:ℝ) < k := by exact_mod_cast (show m < k by omega)
    have hR2 : (k:ℝ) < 2*(m:ℝ) := by exact_mod_cast (show k < 2*m by omega)
    have hmul1 := mul_lt_mul_of_pos_right hR1 ha.1
    have hmul2 := mul_lt_mul_of_pos_right hR2 ha.1
    apply cos_central_band_strict <;> nlinarith

theorem pairX_nonadjacent {n i j : ℕ} (hn : 6 ≤ n) (hij : i+2 ≤ j)
    (hjn : j+2 ≤ n+i) :
    -(1+2*Real.cos (step n))/2 < pairX (angle n i) (angle n j) := by
  have ha := step_bounds hn
  have hc := cos_step_bounds hn
  have hpi := step_mul (show 0 < n by omega)
  have hR1 : (i:ℝ)+2 ≤ j := by exact_mod_cast hij
  have hR2 : (j:ℝ)+2 ≤ (n:ℝ)+i := by exact_mod_cast hjn
  have hmul1 := mul_le_mul_of_nonneg_right hR1 (le_of_lt ha.1)
  have hmul2 := mul_le_mul_of_nonneg_right hR2 (le_of_lt ha.1)
  have habs : |Real.cos (angle n i-angle n j)| ≤ 2*Real.cos (step n)^2-1 := by
    rw [show angle n i-angle n j = -(((j:ℝ)-(i:ℝ))*step n) by
      simp only [angle_eq_step]; ring, Real.cos_neg]
    have h := abs_cos_middle (le_of_lt ha.1)
      (show step n ≤ Real.pi/4 by linarith [Real.pi_pos])
      (x:=((j:ℝ)-(i:ℝ))*step n) (by nlinarith) (by nlinarith)
    simpa only [Real.cos_two_mul] using h
  exact quadratic_nonadjacent hc.1 hc.2 habs

theorem pairX_adjacent_strict {m i : ℕ} (hm : 2 ≤ m) (hi : i+1 < 3*m)
    (him : i+1 ≠ m) (hi2m : i+1 ≠ 2*m) :
    -(1+2*Real.cos (step (3*m)))/2 <
      pairX (angle (3*m) i) (angle (3*m) (i+1)) := by
  have hc := cos_step_bounds (show 6 ≤ 3*m by omega)
  have hsum : angle (3*m) i+angle (3*m) (i+1) =
      2*((i+1:ℕ):ℝ)*step (3*m) := by
    simp only [angle_eq_step,Nat.cast_add,Nat.cast_one]; ring
  have hdiff : angle (3*m) i-angle (3*m) (i+1) = -step (3*m) := by
    simp only [angle_eq_step,Nat.cast_add,Nat.cast_one]; ring
  unfold pairX
  rw [hsum,hdiff,Real.cos_neg]
  exact quadratic_adjacent_strict hc.2 (adjacent_cos_strict hm hi him hi2m)

theorem pairX_eq_vertexX (u v : ℝ) : pairX u v = FurediPalastiChart.vertexX u v := by
  unfold pairX FurediPalastiChart.vertexX
  rw [Real.cos_add_cos]
  rw [show (2*u+2*v)/2=u+v by ring,show (2*u-2*v)/2=u-v by ring]
  rw [show 2*u+2*v=2*(u+v) by ring,Real.cos_two_mul]
  ring

theorem cap_eq_step (n : ℕ) :
    FurediPalastiChart.cap n = 1+2*Real.cos (step n) := by
  unfold FurediPalastiChart.cap
  rw [angle_eq_step]
  norm_num
  congr 1
  ring

def LeftCaps (m i j : ℕ) : Prop :=
  (i+1=m ∧ j=m) ∨ (i+1=2*m ∧ j=2*m)

theorem pairX_adjacent_cap {m i : ℕ} (hm : 2 ≤ m)
    (hi : i+1=m ∨ i+1=2*m) :
    pairX (angle (3*m) i) (angle (3*m) (i+1)) =
      -(1+2*Real.cos (step (3*m)))/2 := by
  have hpi := step_mul (show 0 < 3*m by omega)
  push_cast at hpi
  have hsum : angle (3*m) i+angle (3*m) (i+1) =
      2*((i+1:ℕ):ℝ)*step (3*m) := by
    simp only [angle_eq_step,Nat.cast_add,Nat.cast_one]; ring
  have hdiff : angle (3*m) i-angle (3*m) (i+1) = -step (3*m) := by
    simp only [angle_eq_step,Nat.cast_add,Nat.cast_one]; ring
  have hcos : Real.cos (angle (3*m) i+angle (3*m) (i+1)) = -(1/2) := by
    rw [hsum]
    rcases hi with hi | hi
    · rw [hi]
      rw [show 2*(m:ℝ)*step (3*m)=2*Real.pi/3 by nlinarith]
      exact cos_two_thirds_pi
    · rw [hi]
      push_cast
      rw [show 2*(2*(m:ℝ))*step (3*m)=4*Real.pi/3 by nlinarith]
      exact cos_four_thirds_pi
  unfold pairX
  rw [hcos,hdiff,Real.cos_neg]
  ring

theorem left_cap_value {m i j : ℕ} (hm : 2 ≤ m) (hij : i < j) (hj : j < 3*m)
    (hcap : LeftCaps m i j) :
    (intersection (arrangement (3*m) i) (arrangement (3*m) j)).1 =
      -FurediPalastiChart.cap (3*m)/2 := by
  have hd := noParallel (3*m) ⟨i,by omega⟩ ⟨j,hj⟩ hij
  rw [arrangement,arrangement,FurediPalastiChart.intersection_x _ _ hd,
    ← pairX_eq_vertexX,cap_eq_step]
  have he : j=i+1 := by rcases hcap with h | h <;> omega
  subst j
  exact pairX_adjacent_cap hm (by rcases hcap with h | h <;> simp_all [LeftCaps])

theorem above_left_caps {m i j : ℕ} (hm : 2 ≤ m) (hij : i < j) (hj : j < 3*m)
    (hcap : ¬ LeftCaps m i j) :
    -FurediPalastiChart.cap (3*m)/2 <
      (intersection (arrangement (3*m) i) (arrangement (3*m) j)).1 := by
  by_cases hright : i=0 ∧ j=3*m-1
  · rcases hright with ⟨rfl,rfl⟩
    rw [FurediPalastiChart.cap_vertex (3*m) (by omega),cap_eq_step]
    have hc := cos_step_bounds (show 6 ≤ 3*m by omega)
    linarith [hc.1]
  have hd := noParallel (3*m) ⟨i,by omega⟩ ⟨j,hj⟩ hij
  rw [arrangement,arrangement,FurediPalastiChart.intersection_x _ _ hd,
    ← pairX_eq_vertexX,cap_eq_step]
  by_cases hadj : j=i+1
  · subst j
    apply pairX_adjacent_strict hm hj
    · intro he; exact hcap (Or.inl ⟨he,he⟩)
    · intro he; exact hcap (Or.inr ⟨he,he⟩)
  · exact pairX_nonadjacent (n:=3*m) (i:=i) (j:=j)
      (by omega) (by omega) (by omega)

theorem exists_left_cut (m : ℕ) (hm : 2 ≤ m) :
    ∃ h : ℝ, h<0 ∧ -FurediPalastiChart.cap (3*m)/2<h ∧
      ∀ i j : Fin (3*m), i<j → ¬ LeftCaps m i j →
        h<(intersection (arrangement (3*m) i) (arrangement (3*m) j)).1 := by
  classical
  let f : Fin (3*m) × Fin (3*m) → ℝ := fun p =>
    if p.1<p.2 ∧ ¬ LeftCaps m p.1 p.2
    then -(intersection (arrangement (3*m) p.1) (arrangement (3*m) p.2)).1 else 0
  have hn0 : 0<3*m := by omega
  letI : Nonempty (Fin (3*m)) := ⟨⟨0,hn0⟩⟩
  have hf : ∀ p, f p<FurediPalastiChart.cap (3*m)/2 := by
    intro p
    dsimp [f]
    split
    · rename_i he
      have hv := above_left_caps hm he.1 p.2.isLt he.2
      linarith
    · have hv := FurediPalastiChart.cap_pos (3*m) (by omega)
      linarith
  let M := Finset.univ.sup' Finset.univ_nonempty f
  have hM : M<FurediPalastiChart.cap (3*m)/2 :=
    (Finset.sup'_lt_iff Finset.univ_nonempty).mpr (fun p _ => hf p)
  have hz : 0≤M := by
    have hle := Finset.le_sup' f
      (Finset.mem_univ ((⟨0,hn0⟩:Fin (3*m)),(⟨0,hn0⟩:Fin (3*m))))
    simpa only [f,lt_self_iff_false,false_and,ite_false] using hle
  rcases exists_between hM with ⟨a,hMa,ha⟩
  refine ⟨-a,by linarith,by linarith,?_⟩
  intro i j hij hne
  have hle := Finset.le_sup' f (Finset.mem_univ (i,j))
  have hfij : f (i,j)=-(intersection (arrangement (3*m) i) (arrangement (3*m) j)).1 := by
    simp [f,hij,hne]
  rw [hfij] at hle
  linarith

#print axioms above_left_caps
#print axioms exists_left_cut

end Kobon.FurediPalastiCaps
