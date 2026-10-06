import Kobon.Euclidean
import Kobon.Exterior
import Mathlib.Tactic

/-! Exact normal-sector algebra for the geometric successor construction.
A terminal ray gives same-sign affine evaluations for every transverse line.
These signs force the two supporting critical normal directions to be adjacent,
without trigonometric angles or floating sorting. The finite sector count is a
separate combinatorial layer.
-/
namespace Kobon.OpenMathBoundaryNormals
open Exterior
set_option autoImplicit false
set_option maxHeartbeats 1000000

def direction (l : Line ℝ) : Point := (l.b,-l.a)

def rayPoint (p d : Point) (t : ℝ) : Point := (p.1+t*d.1,p.2+t*d.2)

theorem ray_eval (l : Line ℝ) (p d : Point) (t : ℝ) :
    affineEval l (rayPoint p d t)=affineEval l p+t*projection l d := by
  dsimp [affineEval,rayPoint,projection]
  ring

/-- Geometric avoidance of every forward transverse crossing. -/
def ForwardAvoids (n : Nat) (L : Nat→Line ℝ) (p d : Point) : Prop :=
  ∀ r : Fin n, affineEval (L r) p≠0 → ∀ t : ℝ, 0<t → affineEval (L r) (rayPoint p d t)≠0

/-- The exact sign invariant obtained from a terminal unbounded ray. -/
def TerminalSigns (n : Nat) (L : Nat→Line ℝ) (p d : Point) : Prop :=
  ∀ r : Fin n, affineEval (L r) p≠0 → 0<affineEval (L r) p*projection (L r) d

theorem positive_product_of_no_forward_zero (E D : ℝ) (hE : E≠0) (hD : D≠0)
    (h : ∀ t : ℝ, 0<t → E+t*D≠0) : 0<E*D := by
  by_contra hp
  have hn : E*D<0 := by
    rcases (le_of_not_gt hp).eq_or_lt with hz|hlt
    · exact False.elim ((mul_ne_zero hE hD) hz)
    · exact hlt
  have hid : (-E/D)*D^2= -(E*D) := by field_simp
  have hs : 0<D^2 := sq_pos_of_ne_zero hD
  have ht : 0< -E/D := by
    by_contra ht
    have hm := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt ht) hs.le
    rw [hid] at hm
    linarith
  apply h (-E/D) ht
  rw [div_mul_cancel₀ (-E) hD]
  ring

theorem terminalSigns_of_avoids (n : Nat) (L : Nat→Line ℝ) (p d : Point)
    (h : ForwardAvoids n L p d)
    (hd : ∀ r : Fin n, affineEval (L r) p≠0 → projection (L r) d≠0) :
    TerminalSigns n L p d := by
  intro r hr
  apply positive_product_of_no_forward_zero _ _ hr (hd r hr)
  intro t ht
  simpa only [ray_eval] using h r hr t ht

theorem compatible_directions (n : Nat) (L : Nat→Line ℝ) (p d e : Point)
    (hd : TerminalSigns n L p d) (he : TerminalSigns n L p e)
    (r : Fin n) (hr : affineEval (L r) p≠0) :
    0<projection (L r) d*projection (L r) e := by
  have hm := mul_pos (hd r hr) (he r hr)
  have hid : (affineEval (L r) p*projection (L r) d)*
      (affineEval (L r) p*projection (L r) e)=
      (affineEval (L r) p)^2*(projection (L r) d*projection (L r) e) := by ring
  rw [hid] at hm
  exact (mul_pos_iff_of_pos_left (sq_pos_of_ne_zero hr)).mp hm

def normSquare (l : Line ℝ) : ℝ := l.a^2+l.b^2

def rotatedNormal (l : Line ℝ) : Line ℝ := ⟨-l.b,l.a,0⟩

def normalAt (l : Line ℝ) (s : ℝ) : Line ℝ := ⟨-l.b+s*l.a,l.a+s*l.b,0⟩

noncomputable def critical (base l : Line ℝ) : ℝ := -det l (rotatedNormal base)/det l base

theorem normalAt_determinant (base l : Line ℝ) (s : ℝ) :
    det l (normalAt base s)=det l (rotatedNormal base)+s*det l base := by
  dsimp [normalAt,rotatedNormal,det]
  ring

theorem base_normalAt (base : Line ℝ) (s : ℝ) :
    det base (normalAt base s)=normSquare base := by
  dsimp [normalAt,normSquare,det]
  ring

theorem normalAt_critical (base l : Line ℝ) (h : det l base≠0) :
    det l (normalAt base (critical base l))=0 := by
  rw [normalAt_determinant]
  unfold critical
  rw [div_mul_cancel₀ _ h]
  ring

theorem normalAt_projection (base : Line ℝ) (p : Point) (s : ℝ) :
    projection (normalAt base s) p=projection (rotatedNormal base) p+s*projection base p := by
  dsimp [projection,normalAt,rotatedNormal]
  ring

/-- A normalization identity relating a transverse old normal to its exact
critical representative. Only nonparallelness to the chart pole is needed. -/
theorem critical_projection_identity (base l : Line ℝ) (p : Point) (h : det l base≠0) :
    det l base*projection (normalAt base (critical base l)) p=
      -normSquare base*projection l p := by
  unfold critical
  dsimp [projection,normalAt,rotatedNormal,normSquare]
  field_simp
  dsimp [det]
  ring

theorem critical_projection_product (base l : Line ℝ) (p q : Point) (h : det l base≠0) :
    (det l base)^2*(projection (normalAt base (critical base l)) p*
      projection (normalAt base (critical base l)) q)=
      (normSquare base)^2*(projection l p*projection l q) := by
  calc
    _ = (det l base*projection (normalAt base (critical base l)) p)*
        (det l base*projection (normalAt base (critical base l)) q) := by ring
    _ = (-normSquare base*projection l p)*(-normSquare base*projection l q) := by
      rw [critical_projection_identity base l p h,critical_projection_identity base l q h]
    _ = _ := by ring

theorem critical_projection_positive (base l : Line ℝ) (p q : Point)
    (hn : 0<normSquare base) (h : det l base≠0)
    (hp : 0<projection l p*projection l q) :
    0<projection (normalAt base (critical base l)) p*
      projection (normalAt base (critical base l)) q := by
  have hid := critical_projection_product base l p q h
  have hr := mul_pos (sq_pos_of_pos hn) hp
  rw [← hid] at hr
  exact (mul_pos_iff_of_pos_left (sq_pos_of_ne_zero h)).mp hr

theorem critical_ray_zero (base l : Line ℝ) (p : Point)
    (h : det l base≠0) (hp : projection l p=0) :
    projection (normalAt base (critical base l)) p=0 := by
  have hid := critical_projection_identity base l p h
  rw [hp,mul_zero] at hid
  exact (mul_eq_zero.mp hid).resolve_left h

theorem projection_factor (base l : Line ℝ) (p : Point)
    (h : det l base≠0) (hp : projection l p=0) (s : ℝ) :
    projection (normalAt base s) p=(s-critical base l)*projection base p := by
  have hz := critical_ray_zero base l p h hp
  rw [normalAt_projection] at hz
  rw [normalAt_projection]
  nlinarith

/-- The geometric terminal-ray sign invariant excludes every other old
critical normal from the interval between the two supporting directions. -/
theorem critical_not_between (base l m r : Line ℝ) (p q : Point)
    (hn : 0<normSquare base)
    (hl : det l base≠0) (hm : det m base≠0) (hr : det r base≠0)
    (hp : projection l p=0) (hq : projection m q=0)
    (hbase : 0<projection base p*projection base q)
    (hother : 0<projection r p*projection r q) :
    ¬(critical base l<critical base r ∧ critical base r<critical base m) := by
  have hpos := critical_projection_positive base r p q hn hr hother
  rw [projection_factor base l p hl hp,projection_factor base m q hm hq] at hpos
  intro hbetween
  have hneg := mul_neg_of_pos_of_neg (sub_pos.mpr hbetween.1) (sub_neg.mpr hbetween.2)
  have hprod := mul_neg_of_pos_of_neg hbase hneg
  have heq : (projection base p*projection base q)*
      ((critical base r-critical base l)*(critical base r-critical base m))=
      ((critical base r-critical base l)*projection base p)*
      ((critical base r-critical base m)*projection base q) := by ring
  rw [heq] at hprod
  exact (not_lt_of_ge hpos.le) hprod

#print axioms terminalSigns_of_avoids
#print axioms compatible_directions
#print axioms critical_not_between
end Kobon.OpenMathBoundaryNormals