import Kobon.Simple
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Rat.BigOperators
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-! Rational boxes certify entire families of real line arrangements. -/
namespace Kobon.Parametric

abbrev Form (d : Nat) := Fin d → ℚ

def evaluate {d : Nat} (f : Form d) (x : Fin d → ℝ) : ℝ :=
  ∑ i, (f i : ℝ)*x i

def scale {d : Nat} (c : ℚ) (f : Form d) : Form d := fun i => c*f i

@[simp] theorem evaluate_add {d : Nat} (f g : Form d) (x : Fin d → ℝ) :
    evaluate (f+g) x = evaluate f x+evaluate g x := by
  simp [evaluate,add_mul,Finset.sum_add_distrib]

@[simp] theorem evaluate_sub {d : Nat} (f g : Form d) (x : Fin d → ℝ) :
    evaluate (f-g) x = evaluate f x-evaluate g x := by
  simp [evaluate,sub_mul,Finset.sum_sub_distrib]

@[simp] theorem evaluate_scale {d : Nat} (c : ℚ) (f : Form d) (x : Fin d → ℝ) :
    evaluate (scale c f) x = (c:ℝ)*evaluate f x := by
  simp [evaluate,scale,mul_assoc,Finset.mul_sum]

def lower {d : Nat} (lo hi f : Form d) : ℚ :=
  ∑ i, if 0 ≤ f i then f i*lo i else f i*hi i

def upper {d : Nat} (lo hi f : Form d) : ℚ :=
  ∑ i, if 0 ≤ f i then f i*hi i else f i*lo i

def InBox {d : Nat} (lo hi : Form d) (x : Fin d → ℝ) : Prop :=
  ∀ i, (lo i : ℝ) ≤ x i ∧ x i ≤ (hi i : ℝ)

theorem lower_le {d : Nat} (lo hi f : Form d) (x : Fin d → ℝ)
    (hx : InBox lo hi x) : (lower lo hi f : ℝ) ≤ evaluate f x := by
  unfold lower evaluate
  push_cast
  apply Finset.sum_le_sum
  intro i _
  split_ifs with h
  · have hc : (0:ℝ) ≤ (f i:ℝ) := by exact_mod_cast h
    simpa only [Rat.cast_mul] using mul_le_mul_of_nonneg_left (hx i).1 hc
  · have hc : (f i:ℝ) ≤ 0 := by exact_mod_cast (le_of_not_ge h)
    simpa only [Rat.cast_mul] using mul_le_mul_of_nonpos_left (hx i).2 hc

theorem le_upper {d : Nat} (lo hi f : Form d) (x : Fin d → ℝ)
    (hx : InBox lo hi x) : evaluate f x ≤ (upper lo hi f : ℝ) := by
  unfold upper evaluate
  push_cast
  apply Finset.sum_le_sum
  intro i _
  split_ifs with h
  · have hc : (0:ℝ) ≤ (f i:ℝ) := by exact_mod_cast h
    simpa only [Rat.cast_mul] using mul_le_mul_of_nonneg_left (hx i).2 hc
  · have hc : (f i:ℝ) ≤ 0 := by exact_mod_cast (le_of_not_ge h)
    simpa only [Rat.cast_mul] using mul_le_mul_of_nonpos_left (hx i).1 hc

theorem nonneg_of_lower {d : Nat} (lo hi f : Form d) (x : Fin d → ℝ)
    (hx : InBox lo hi x) (h : 0 ≤ lower lo hi f) : 0 ≤ evaluate f x := by
  exact le_trans (by exact_mod_cast h) (lower_le lo hi f x hx)

theorem nonpos_of_upper {d : Nat} (lo hi f : Form d) (x : Fin d → ℝ)
    (hx : InBox lo hi x) (h : upper lo hi f ≤ 0) : evaluate f x ≤ 0 := by
  exact le_trans (le_upper lo hi f x hx) (by exact_mod_cast h)

def NonzeroCert {d : Nat} (lo hi f : Form d) (e : Fin d) : Prop :=
  0 < lower lo hi f ∨ upper lo hi f < 0 ∨
    ((∀ i, i ≠ e → f i=0) ∧ f e ≠ 0)

instance {d : Nat} (lo hi f : Form d) (e : Fin d) : Decidable (NonzeroCert lo hi f e) := by
  unfold NonzeroCert
  infer_instance

theorem nonzero_of_cert {d : Nat} (lo hi f : Form d) (e : Fin d) (x : Fin d → ℝ)
    (hx : InBox lo hi x) (he : 0 < x e) (h : NonzeroCert lo hi f e) :
    evaluate f x ≠ 0 := by
  rcases h with hp | hn | ⟨hz,he'⟩
  · exact ne_of_gt (lt_of_lt_of_le (by exact_mod_cast hp) (lower_le lo hi f x hx))
  · exact ne_of_lt (lt_of_le_of_lt (le_upper lo hi f x hx) (by exact_mod_cast hn))
  · have hsum : evaluate f x = (f e : ℝ)*x e := by
      unfold evaluate
      apply Finset.sum_eq_single e
      · intro i _ hie
        simp [hz i hie]
      · simp
    rw [hsum]
    exact mul_ne_zero (by exact_mod_cast he') (ne_of_gt he)

structure ParamLine (d : Nat) where
  a : ℚ
  b : ℚ
  c : Form d
  deriving Inhabited

def toLine {d : Nat} (l : ParamLine d) (x : Fin d → ℝ) : Line ℝ :=
  ⟨l.a,l.b,evaluate l.c x⟩

def determinant {d : Nat} (l m : ParamLine d) : ℚ := l.a*m.b-l.b*m.a

def evalForm {d : Nat} (r l m : ParamLine d) : Form d :=
  scale r.a (scale m.b l.c-scale l.b m.c)+
  scale r.b (scale l.a m.c-scale m.a l.c)-scale (determinant l m) r.c

def orientedForm {d : Nat} (r l m : ParamLine d) : Form d :=
  scale (determinant l m) (evalForm r l m)

@[simp] theorem determinant_value {d : Nat} (l m : ParamLine d) (x : Fin d → ℝ) :
    det (toLine l x) (toLine m x) = (determinant l m : ℝ) := by
  simp [det,toLine,determinant]

@[simp] theorem evalForm_value {d : Nat} (r l m : ParamLine d) (x : Fin d → ℝ) :
    evaluate (evalForm r l m) x = evalVertex (toLine r x) (toLine l x) (toLine m x) := by
  simp [evalForm,evalVertex,vertex,det,toLine,determinant]
  ring

@[simp] theorem orientedForm_value {d : Nat} (r l m : ParamLine d) (x : Fin d → ℝ) :
    evaluate (orientedForm r l m) x = orientedEval (toLine r x) (toLine l x) (toLine m x) := by
  simp [orientedForm,orientedEval,mul_comm]

def DirectionCheck {d : Nat} (n : Nat) (L : Nat → ParamLine d) : Prop :=
  ∀ i j : Fin n, i<j → determinant (L i) (L j) ≠ 0

def SimpleCheck {d : Nat} (n : Nat) (lo hi : Form d) (e : Fin d) (L : Nat → ParamLine d) : Prop :=
  ∀ i j k : Fin n, i<j → j<k → NonzeroCert lo hi (evalForm (L k) (L i) (L j)) e

def TriangleCheck {d : Nat} (n : Nat) (lo hi : Form d) (L : Nat → ParamLine d) (t : Triple) : Prop :=
  t.i<t.j ∧ t.j<t.k ∧ t.k<n ∧ ∀ r : Fin n,
    (0 ≤ lower lo hi (orientedForm (L r) (L t.i) (L t.j)) ∧
     0 ≤ lower lo hi (orientedForm (L r) (L t.i) (L t.k)) ∧
     0 ≤ lower lo hi (orientedForm (L r) (L t.j) (L t.k))) ∨
    (upper lo hi (orientedForm (L r) (L t.i) (L t.j)) ≤ 0 ∧
     upper lo hi (orientedForm (L r) (L t.i) (L t.k)) ≤ 0 ∧
     upper lo hi (orientedForm (L r) (L t.j) (L t.k)) ≤ 0)

instance {d : Nat} (n : Nat) (L : Nat → ParamLine d) : Decidable (DirectionCheck n L) := by
  unfold DirectionCheck
  infer_instance
instance {d : Nat} (n : Nat) (lo hi : Form d) (e : Fin d) (L : Nat → ParamLine d) :
    Decidable (SimpleCheck n lo hi e L) := by
  unfold SimpleCheck
  infer_instance
instance {d : Nat} (n : Nat) (lo hi : Form d) (L : Nat → ParamLine d) (t : Triple) :
    Decidable (TriangleCheck n lo hi L t) := by
  unfold TriangleCheck
  infer_instance

theorem directions_sound {d : Nat} (n : Nat) (L : Nat → ParamLine d)
    (x : Fin d → ℝ) (h : DirectionCheck n L) : NoParallel n (fun i => toLine (L i) x) := by
  intro i j hij
  simpa using h i j hij

theorem simple_sound {d : Nat} (n : Nat) (lo hi : Form d) (e : Fin d) (L : Nat → ParamLine d)
    (x : Fin d → ℝ) (hx : InBox lo hi x) (he : 0 < x e) (h : SimpleCheck n lo hi e L) :
    NoConcurrent n (fun i => toLine (L i) x) := by
  intro i j k hij hjk
  simpa using nonzero_of_cert lo hi (evalForm (L k) (L i) (L j)) e x hx he (h i j k hij hjk)

theorem triangle_sound {d : Nat} (n : Nat) (lo hi : Form d) (e : Fin d) (L : Nat → ParamLine d)
    (x : Fin d → ℝ) (hx : InBox lo hi x) (he : 0 < x e)
    (hs : SimpleCheck n lo hi e L) (t : Triple) (ht : TriangleCheck n lo hi L t) :
    TrianglePredicate n (fun i => toLine (L i) x) t := by
  rcases ht with ⟨hij,hjk,hkn,ht⟩
  refine ⟨hij,hjk,hkn,?_,?_⟩
  · have h := simple_sound n lo hi e L x hx he hs
    exact h ⟨t.i,by omega⟩ ⟨t.j,by omega⟩ ⟨t.k,hkn⟩ hij hjk
  · intro r
    rcases ht r with ⟨h1,h2,h3⟩ | ⟨h1,h2,h3⟩
    · left
      exact ⟨by simpa using nonneg_of_lower lo hi _ x hx h1,
        by simpa using nonneg_of_lower lo hi _ x hx h2,
        by simpa using nonneg_of_lower lo hi _ x hx h3⟩
    · right
      exact ⟨by simpa using nonpos_of_upper lo hi _ x hx h1,
        by simpa using nonpos_of_upper lo hi _ x hx h2,
        by simpa using nonpos_of_upper lo hi _ x hx h3⟩

#print axioms triangle_sound
#print axioms simple_sound

end Kobon.Parametric
