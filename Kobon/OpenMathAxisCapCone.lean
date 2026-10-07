import Kobon.Euclidean
import Mathlib.Tactic

/-! A convex, linear feasibility model for saturated-axis constructions.
The lines are `x - u_i*y = a_i` and the distinguished line is `y = 0`.
Once the above/below choice of every consecutive axis cap is fixed, all
constraints are linear in the reciprocal slopes `u`. This module proves
both convexity and actual empty-triangle soundness, without an LP oracle.
-/
namespace Kobon.OpenMathAxisCapCone
set_option autoImplicit false
set_option maxHeartbeats 2000000

def axis : Line ℝ := ⟨0,1,0⟩
def reciprocalLine (a u : Nat → ℝ) (i : Nat) : Line ℝ := ⟨1,-u i,a i⟩
def arrangement (a u : Nat → ℝ) (i : Nat) : Line ℝ :=
  if i=0 then axis else reciprocalLine a u (i-1)

def wall (a u : Nat → ℝ) (j r : Nat) : ℝ :=
  (a (j+1)-a r)*u j+(a r-a j)*u (j+1)+(a j-a (j+1))*u r

/-- All inequalities are linear in `u`; the Boolean records the side of Y0. -/
def CapRegion (q : Nat) (a : Nat → ℝ) (above : Nat → Bool) (u : Nat → ℝ) : Prop :=
  ∀ j, j+1<q →
    if above j then
      0<u j-u (j+1) ∧ ∀ r, r<q →
        (r<j → 0≤wall a u j r) ∧ (j+1<r → wall a u j r≤0)
    else
      u j-u (j+1)<0 ∧ ∀ r, r<q →
        (r<j → wall a u j r≤0) ∧ (j+1<r → 0≤wall a u j r)

def mix (t : ℝ) (u v : Nat → ℝ) : Nat → ℝ := fun i => (1-t)*u i+t*v i

theorem wall_mix (a u v : Nat → ℝ) (t : ℝ) (j r : Nat) :
    wall a (mix t u v) j r=(1-t)*wall a u j r+t*wall a v j r := by
  dsimp [wall,mix]
  ring

theorem difference_mix (u v : Nat → ℝ) (t : ℝ) (j : Nat) :
    mix t u v j-mix t u v (j+1)=(1-t)*(u j-u (j+1))+t*(v j-v (j+1)) := by
  dsimp [mix]
  ring

theorem mix_pos (x y t : ℝ) (hx : 0<x) (hy : 0<y)
    (ht : 0≤t) (ht1 : t≤1) : 0<(1-t)*x+t*y := by
  by_cases he : t=1
  · simpa [he] using hy
  · have hp : 0<1-t := sub_pos.mpr (lt_of_le_of_ne ht1 he)
    exact add_pos_of_pos_of_nonneg (mul_pos hp hx) (mul_nonneg ht hy.le)

theorem mix_neg (x y t : ℝ) (hx : x<0) (hy : y<0)
    (ht : 0≤t) (ht1 : t≤1) : (1-t)*x+t*y<0 := by
  have hh := mix_pos (-x) (-y) t (by linarith) (by linarith) ht ht1
  nlinarith

/-- Convex interpolation keeps every cap wall and its strict orientation. -/
theorem capRegion_convex (q : Nat) (a : Nat → ℝ) (above : Nat → Bool)
    (u v : Nat → ℝ) (hu : CapRegion q a above u) (hv : CapRegion q a above v)
    (t : ℝ) (ht : 0≤t) (ht1 : t≤1) : CapRegion q a above (mix t u v) := by
  intro j hj
  have h1 := hu j hj
  have h2 := hv j hj
  have hw : 0≤1-t := by linarith
  cases ha : above j <;> simp only [ha,Bool.false_eq_true,if_false,if_true] at h1 h2 ⊢
  · refine ⟨?_,?_⟩
    · rw [difference_mix]
      exact mix_neg _ _ t h1.1 h2.1 ht ht1
    · intro r hr
      constructor
      · intro hrl
        rw [wall_mix]
        exact add_nonpos (mul_nonpos_of_nonneg_of_nonpos hw ((h1.2 r hr).1 hrl))
          (mul_nonpos_of_nonneg_of_nonpos ht ((h2.2 r hr).1 hrl))
      · intro hrr
        rw [wall_mix]
        exact add_nonneg (mul_nonneg hw ((h1.2 r hr).2 hrr))
          (mul_nonneg ht ((h2.2 r hr).2 hrr))
  · refine ⟨?_,?_⟩
    · rw [difference_mix]
      exact mix_pos _ _ t h1.1 h2.1 ht ht1
    · intro r hr
      constructor
      · intro hrl
        rw [wall_mix]
        exact add_nonneg (mul_nonneg hw ((h1.2 r hr).1 hrl))
          (mul_nonneg ht ((h2.2 r hr).1 hrl))
      · intro hrr
        rw [wall_mix]
        exact add_nonpos (mul_nonpos_of_nonneg_of_nonpos hw ((h1.2 r hr).2 hrr))
          (mul_nonpos_of_nonneg_of_nonpos ht ((h2.2 r hr).2 hrr))

@[simp] theorem wall_self_left (a u : Nat → ℝ) (j : Nat) : wall a u j j=0 := by
  dsimp [wall]
  ring

@[simp] theorem wall_self_right (a u : Nat → ℝ) (j : Nat) : wall a u j (j+1)=0 := by
  dsimp [wall]
  ring

theorem capRegion_products (q : Nat) (a : Nat → ℝ) (above : Nat → Bool)
    (u : Nat → ℝ) (hu : CapRegion q a above u) (j : Nat) (hj : j+1<q) :
    u j-u (j+1)≠0 ∧ ∀ r, r<q →
      (r<j → 0≤wall a u j r*(u j-u (j+1))) ∧
      (j+1<r → wall a u j r*(u j-u (j+1))≤0) := by
  have h := hu j hj
  cases ha : above j <;> simp only [ha,Bool.false_eq_true,if_false,if_true] at h
  · refine ⟨ne_of_lt h.1,?_⟩
    intro r hr
    exact ⟨fun hl => mul_nonneg_of_nonpos_of_nonpos ((h.2 r hr).1 hl) h.1.le,
      fun hh => mul_nonpos_of_nonneg_of_nonpos ((h.2 r hr).2 hh) h.1.le⟩
  · refine ⟨ne_of_gt h.1,?_⟩
    intro r hr
    exact ⟨fun hl => mul_nonneg ((h.2 r hr).1 hl) h.1.le,
      fun hh => mul_nonpos_of_nonpos_of_nonneg ((h.2 r hr).2 hh) h.1.le⟩

theorem axis_oriented (a u : Nat → ℝ) (i r : Nat) :
    orientedEval (reciprocalLine a u r) axis (reciprocalLine a u i)=a i-a r := by
  dsimp [orientedEval,evalVertex,vertex,det,axis,reciprocalLine]
  ring

theorem cap_oriented (a u : Nat → ℝ) (j r : Nat) :
    orientedEval (reciprocalLine a u r) (reciprocalLine a u j)
      (reciprocalLine a u (j+1))=wall a u j r*(u j-u (j+1)) := by
  dsimp [orientedEval,evalVertex,vertex,det,reciprocalLine,wall]
  ring

/-- Every feasible consecutive cap is an actual empty nondegenerate triangle. -/
theorem capRegion_triangle (q : Nat) (a : Nat → ℝ) (above : Nat → Bool)
    (u : Nat → ℝ) (ha : StrictMonoOn a (Set.Iio q))
    (hu : CapRegion q a above u) (j : Nat) (hj : j+1<q) :
    TrianglePredicate (q+1) (arrangement a u) ⟨0,j+1,j+2⟩ := by
  have hajn : j<q := by omega
  have haj : a j<a (j+1) := ha hajn hj (by omega)
  have hp := capRegion_products q a above u hu j hj
  unfold TrianglePredicate
  dsimp only
  refine ⟨by omega,by omega,by omega,?_,?_⟩
  · simp only [arrangement,show j+1≠0 by omega,show j+2≠0 by omega,
      if_false,if_true,Nat.add_sub_cancel,show j+2-1=j+1 by omega]
    dsimp [evalVertex,vertex,det,axis,reciprocalLine]
    linarith
  · intro r
    by_cases hz : r.val=0
    · simp only [hz,arrangement,show j+1≠0 by omega,show j+2≠0 by omega,
        if_false,if_true,Nat.add_sub_cancel,show j+2-1=j+1 by omega]
      dsimp [orientedEval,evalVertex,vertex,det,axis,reciprocalLine]
      rcases le_total 0 ((a (j+1)-a j)*(u j-u (j+1))) with h | h
      · left; constructor; · norm_num
        constructor; · norm_num
        nlinarith only [h]
      · right; constructor; · norm_num
        constructor; · norm_num
        nlinarith only [h]
    · have hr : r.val-1<q := by have := r.isLt; omega
      simp only [arrangement,hz,if_false,if_true,show j+1≠0 by omega,show j+2≠0 by omega,
        Nat.add_sub_cancel,show j+2-1=j+1 by omega,axis_oriented,cap_oriented]
      by_cases hl : r.val-1<j
      · have har : a (r.val-1)<a j := ha hr hajn hl
        exact Or.inl ⟨by linarith,by linarith,(hp.2 _ hr).1 hl⟩
      · by_cases hh : j+1<r.val-1
        · have har : a (j+1)<a (r.val-1) := ha hj hr hh
          exact Or.inr ⟨by linarith,by linarith,(hp.2 _ hr).2 hh⟩
        · have he : r.val-1=j ∨ r.val-1=j+1 := by omega
          rcases he with he | he
          · simp only [he,sub_self,wall_self_left,zero_mul]
            exact Or.inl ⟨le_rfl,by linarith,le_rfl⟩
          · simp only [he,sub_self,wall_self_right,zero_mul]
            exact Or.inr ⟨by linarith,le_rfl,le_rfl⟩

def DirectionPattern (q : Nat) (above : Nat → Bool) (u : Nat → ℝ) : Prop :=
  ∀ j, j+1<q → if above j then 0<u j-u (j+1) else u j-u (j+1)<0

theorem cap_products_of_triangle (q : Nat) (a u : Nat → ℝ)
    (ha : StrictMonoOn a (Set.Iio q)) (j : Nat) (hj : j+1<q)
    (hc : TrianglePredicate (q+1) (arrangement a u) ⟨0,j+1,j+2⟩) :
    ∀ r, r<q → (r<j → 0≤wall a u j r*(u j-u (j+1))) ∧
      (j+1<r → wall a u j r*(u j-u (j+1))≤0) := by
  intro r hr
  have he := hc.2.2.2.2 (⟨r+1,by omega⟩ : Fin (q+1))
  dsimp only at he
  simp only [arrangement,show r+1≠0 by omega,show j+1≠0 by omega,
    show j+2≠0 by omega,if_false,if_true,Nat.add_sub_cancel,
    show j+2-1=j+1 by omega,axis_oriented,cap_oriented] at he
  constructor
  · intro hrl
    have hjn : j<q := by omega
    have har : a r<a j := ha hr hjn hrl
    rcases he with he | he
    · exact he.2.2
    · exfalso; linarith [he.1]
  · intro hrr
    have har : a (j+1)<a r := ha hj hr hrr
    rcases he with he | he
    · exfalso; linarith [he.2.1]
    · exact he.2.2

theorem right_pos_nonneg (x d : ℝ) (hd : 0<d) (h : 0≤x*d) : 0≤x := by
  by_contra hx
  have hh := mul_neg_of_neg_of_pos (lt_of_not_ge hx) hd
  linarith

theorem right_pos_nonpos (x d : ℝ) (hd : 0<d) (h : x*d≤0) : x≤0 := by
  by_contra hx
  have hh := mul_pos (lt_of_not_ge hx) hd
  linarith

theorem right_neg_nonpos (x d : ℝ) (hd : d<0) (h : 0≤x*d) : x≤0 := by
  by_contra hx
  have hh := mul_neg_of_pos_of_neg (lt_of_not_ge hx) hd
  linarith

theorem right_neg_nonneg (x d : ℝ) (hd : d<0) (h : x*d≤0) : 0≤x := by
  by_contra hx
  have hh := mul_pos_of_neg_of_neg (lt_of_not_ge hx) hd
  linarith

/-- With the cap orientations fixed, the linear model is geometrically exact. -/
theorem capRegion_iff (q : Nat) (a : Nat → ℝ) (above : Nat → Bool)
    (u : Nat → ℝ) (ha : StrictMonoOn a (Set.Iio q))
    (hd : DirectionPattern q above u) :
    CapRegion q a above u ↔ ∀ j, j+1<q →
      TrianglePredicate (q+1) (arrangement a u) ⟨0,j+1,j+2⟩ := by
  constructor
  · exact fun hu j hj => capRegion_triangle q a above u ha hu j hj
  · intro hc j hj
    have hp := cap_products_of_triangle q a u ha j hj (hc j hj)
    have hdir := hd j hj
    cases hh : above j <;> simp only [hh,Bool.false_eq_true,if_false,if_true] at hdir ⊢
    · refine ⟨hdir,?_⟩
      intro r hr
      exact ⟨fun hl => right_neg_nonpos _ _ hdir ((hp r hr).1 hl),
        fun hr' => right_neg_nonneg _ _ hdir ((hp r hr).2 hr')⟩
    · refine ⟨hdir,?_⟩
      intro r hr
      exact ⟨fun hl => right_pos_nonneg _ _ hdir ((hp r hr).1 hl),
        fun hr' => right_pos_nonpos _ _ hdir ((hp r hr).2 hr')⟩

#print axioms capRegion_convex
#print axioms capRegion_triangle
#print axioms capRegion_iff
end Kobon.OpenMathAxisCapCone
