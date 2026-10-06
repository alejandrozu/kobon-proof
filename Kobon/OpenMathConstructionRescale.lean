import Kobon.OpenMathConstructionBooleanMemo

/-! Denominator clearing for exact parametric line certificates.
Every supporting line may be multiplied by an arbitrary positive rational.
All finite geometric box checks are preserved. The native decisions can then
use integer coefficients instead of normalizing products of many unrelated
rational denominators; the soundness bridges remain ordinary kernel proofs.
-/
namespace Kobon.OpenMathConstructionRescale
open Parametric HybridBoundary
set_option autoImplicit false
set_option maxHeartbeats 1000000

def rescale {d : Nat} (s : ℚ) (l : ParamLine d) : ParamLine d :=
  ⟨s*l.a,s*l.b,scale s l.c⟩

theorem determinant_rescale {d : Nat} (s t : ℚ) (l m : ParamLine d) :
    determinant (rescale s l) (rescale t m)=s*t*determinant l m := by
  simp only [rescale,determinant]
  ring

theorem evalForm_rescale {d : Nat} (u s t : ℚ) (r l m : ParamLine d) :
    evalForm (rescale u r) (rescale s l) (rescale t m)=scale (u*s*t) (evalForm r l m) := by
  funext i
  dsimp [evalForm,rescale,scale,determinant]
  ring

theorem orientedForm_rescale {d : Nat} (u s t : ℚ) (r l m : ParamLine d) :
    orientedForm (rescale u r) (rescale s l) (rescale t m)=
      scale (u*(s*t)^2) (orientedForm r l m) := by
  funext i
  dsimp [orientedForm,evalForm,rescale,scale,determinant]
  ring

theorem lower_scale {d : Nat} (lo hi f : Form d) (s : ℚ) (hs : 0<s) :
    lower lo hi (scale s f)=s*lower lo hi f := by
  unfold lower
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hf : 0≤f i
  · have hsf : 0≤s*f i := mul_nonneg hs.le hf
    simp only [scale,if_pos hf,if_pos hsf]
    ring
  · have hsf : ¬0≤s*f i := not_le_of_gt (mul_neg_of_pos_of_neg hs (lt_of_not_ge hf))
    simp only [scale,if_neg hf,if_neg hsf]
    ring

theorem upper_scale {d : Nat} (lo hi f : Form d) (s : ℚ) (hs : 0<s) :
    upper lo hi (scale s f)=s*upper lo hi f := by
  unfold upper
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hf : 0≤f i
  · have hsf : 0≤s*f i := mul_nonneg hs.le hf
    simp only [scale,if_pos hf,if_pos hsf]
    ring
  · have hsf : ¬0≤s*f i := not_le_of_gt (mul_neg_of_pos_of_neg hs (lt_of_not_ge hf))
    simp only [scale,if_neg hf,if_neg hsf]
    ring

theorem negative_of_positive_product (s x : ℚ) (hs : 0<s) (h : s*x<0) : x<0 := by
  by_contra hx
  have hn := mul_nonneg hs.le (le_of_not_gt hx)
  exact (not_lt_of_ge hn) h

theorem nonpos_of_positive_product (s x : ℚ) (hs : 0<s) (h : s*x≤0) : x≤0 := by
  by_contra hx
  have hp := mul_pos hs (lt_of_not_ge hx)
  exact (not_lt_of_ge h) hp
theorem nonzero_descaling {d : Nat} (lo hi f : Form d) (e : Fin d)
    (s : ℚ) (hs : 0<s) (h : NonzeroCert lo hi (scale s f) e) : NonzeroCert lo hi f e := by
  rcases h with hp | hn | ⟨hz,he⟩
  · rw [lower_scale lo hi f s hs] at hp
    exact Or.inl ((mul_pos_iff_of_pos_left hs).mp hp)
  · rw [upper_scale lo hi f s hs] at hn
    exact Or.inr (Or.inl (negative_of_positive_product _ _ hs hn))
  · refine Or.inr (Or.inr ⟨?_,?_⟩)
    · intro i hie
      have hh := hz i hie
      dsimp only [scale] at hh
      exact (mul_eq_zero.mp hh).resolve_left hs.ne'
    · intro hf
      exact he (by simp [scale,hf])

theorem directions_descaling {d : Nat} (n : Nat) (L : Nat→ParamLine d) (s : Nat→ℚ)
    (h : DirectionCheck n (fun i => rescale (s i) (L i))) : DirectionCheck n L := by
  intro i j hij
  have hh := h i j hij
  rw [determinant_rescale] at hh
  intro hz
  exact hh (by simp only [hz,mul_zero])

theorem simple_descaling {d : Nat} (n : Nat) (lo hi : Form d) (e : Fin d)
    (L : Nat→ParamLine d) (s : Nat→ℚ) (hs : ∀ i, 0<s i)
    (h : SimpleCheck n lo hi e (fun i => rescale (s i) (L i))) : SimpleCheck n lo hi e L := by
  intro i j k hij hjk
  have hh := h i j k hij hjk
  rw [evalForm_rescale] at hh
  exact nonzero_descaling lo hi _ e _ (mul_pos (mul_pos (hs k) (hs i)) (hs j)) hh

theorem triangle_descaling {d : Nat} (n : Nat) (lo hi : Form d)
    (L : Nat→ParamLine d) (s : Nat→ℚ) (hs : ∀ i, 0<s i) (t : Triple)
    (h : TriangleCheck n lo hi (fun i => rescale (s i) (L i)) t) :
    TriangleCheck n lo hi L t := by
  rcases h with ⟨hi,hj,hk,hr⟩
  refine ⟨hi,hj,hk,?_⟩
  intro r
  have pf : 0<s r*(s t.i*s t.j)^2 := mul_pos (hs r) (sq_pos_of_pos (mul_pos (hs t.i) (hs t.j)))
  have pg : 0<s r*(s t.i*s t.k)^2 := mul_pos (hs r) (sq_pos_of_pos (mul_pos (hs t.i) (hs t.k)))
  have ph : 0<s r*(s t.j*s t.k)^2 := mul_pos (hs r) (sq_pos_of_pos (mul_pos (hs t.j) (hs t.k)))
  rcases hr r with ⟨h1,h2,h3⟩ | ⟨h1,h2,h3⟩
  · left
    rw [orientedForm_rescale,lower_scale _ _ _ _ pf] at h1
    rw [orientedForm_rescale,lower_scale _ _ _ _ pg] at h2
    rw [orientedForm_rescale,lower_scale _ _ _ _ ph] at h3
    exact ⟨(mul_nonneg_iff_of_pos_left pf).mp h1,(mul_nonneg_iff_of_pos_left pg).mp h2,
      (mul_nonneg_iff_of_pos_left ph).mp h3⟩
  · right
    rw [orientedForm_rescale,upper_scale _ _ _ _ pf] at h1
    rw [orientedForm_rescale,upper_scale _ _ _ _ pg] at h2
    rw [orientedForm_rescale,upper_scale _ _ _ _ ph] at h3
    exact ⟨nonpos_of_positive_product _ _ pf h1,nonpos_of_positive_product _ _ pg h2,
      nonpos_of_positive_product _ _ ph h3⟩

theorem derivative_rescale {d : Nat} (u s : ℚ) (r l : ParamLine d) (a b : ℚ) :
    derivativeNumerator (rescale u r) (rescale s l) a b=u*s^2*derivativeNumerator r l a b := by
  dsimp [derivativeNumerator,determinant,rescale]
  ring

theorem visible_descaling {d : Nat} (n : Nat) (lo hi : Form d)
    (L : Nat→ParamLine d) (s : Nat→ℚ) (hs : ∀ i, 0<s i) (a b : ℚ) (t : Triple)
    (h : VisibleCheck n lo hi (fun i => rescale (s i) (L i)) a b t) :
    VisibleCheck n lo hi L a b t := by
  rcases h with ⟨hi,hj,hk,hr⟩
  refine ⟨hi,hj,hk,?_⟩
  intro r
  have pf : 0<s r*(s t.i*s t.j)^2 := mul_pos (hs r) (sq_pos_of_pos (mul_pos (hs t.i) (hs t.j)))
  have pi : 0<s r*(s t.i)^2 := mul_pos (hs r) (sq_pos_of_pos (hs t.i))
  have pj : 0<s r*(s t.j)^2 := mul_pos (hs r) (sq_pos_of_pos (hs t.j))
  rcases hr r with ⟨h1,h2,h3⟩ | ⟨h1,h2,h3⟩
  · left
    rw [orientedForm_rescale,lower_scale _ _ _ _ pf] at h1
    rw [derivative_rescale] at h2 h3
    exact ⟨(mul_nonneg_iff_of_pos_left pf).mp h1,(mul_nonneg_iff_of_pos_left pi).mp h2,
      (mul_nonneg_iff_of_pos_left pj).mp h3⟩
  · right
    rw [orientedForm_rescale,upper_scale _ _ _ _ pf] at h1
    rw [derivative_rescale] at h2 h3
    exact ⟨nonpos_of_positive_product _ _ pf h1,nonpos_of_positive_product _ _ pi h2,
      nonpos_of_positive_product _ _ pj h3⟩

theorem admissible_descaling {d : Nat} (n : Nat) (L : Nat→ParamLine d)
    (s : Nat→ℚ) (a b : ℚ) (h : AdmissibleCheck n (fun i => rescale (s i) (L i)) a b) :
    AdmissibleCheck n L a b := by
  intro i
  have hh := h i
  change (s i*(L i).a)*b-(s i*(L i).b)*a≠0 at hh
  intro hz
  apply hh
  calc
    (s i*(L i).a)*b-(s i*(L i).b)*a = s i*((L i).a*b-(L i).b*a) := by ring
    _ = 0 := by simp only [hz,mul_zero]

def multiplier {d : Nat} (l : ParamLine d) : ℚ :=
  (l.a.den*l.b.den*(∏ i : Fin d, (l.c i).den) : Nat)

theorem multiplier_positive {d : Nat} (l : ParamLine d) : 0<multiplier l := by
  have hp : 0<∏ i : Fin d, (l.c i).den := Finset.prod_pos (fun i _ => (l.c i).den_pos)
  have hn := Nat.mul_pos (Nat.mul_pos l.a.den_pos l.b.den_pos) hp
  unfold multiplier
  exact_mod_cast hn

def clearLine {d : Nat} (l : ParamLine d) : ParamLine d := rescale (multiplier l) l

def clearedSimpleBool {d : Nat} (n : Nat) (lo hi : Form d) (e : Fin d)
    (L : Nat→ParamLine d) : Bool :=
  OpenMathConstructionBooleanMemo.simpleBool n lo hi e (fun i => clearLine (L i))

theorem clearedSimple_sound {d : Nat} (n : Nat) (lo hi : Form d) (e : Fin d)
    (L : Nat→ParamLine d) (h : clearedSimpleBool n lo hi e L=true) : SimpleCheck n lo hi e L := by
  have hh := OpenMathConstructionBooleanMemo.simple_sound n lo hi e (fun i => clearLine (L i)) h
  exact simple_descaling n lo hi e L (fun i => multiplier (L i))
    (fun i => multiplier_positive (L i)) hh

def clearedTrianglesBool {d : Nat} (n : Nat) (lo hi : Form d)
    (L : Nat→ParamLine d) (ts : List Triple) : Bool :=
  OpenMathConstructionBooleanMemo.trianglesBool n lo hi (fun i => clearLine (L i)) ts

theorem clearedTriangles_sound {d : Nat} (n : Nat) (lo hi : Form d)
    (L : Nat→ParamLine d) (ts : List Triple) (h : clearedTrianglesBool n lo hi L ts=true) :
    ts.all (fun t => decide (TriangleCheck n lo hi L t))=true := by
  have hh := OpenMathConstructionBooleanMemo.triangles_sound n lo hi (fun i => clearLine (L i)) ts h
  apply List.all_eq_true.mpr
  intro t ht
  apply decide_eq_true
  exact triangle_descaling n lo hi L (fun i => multiplier (L i))
    (fun i => multiplier_positive (L i)) t (of_decide_eq_true ((List.all_eq_true.mp hh) t ht))

def clearedVisiblesBool {d : Nat} (n : Nat) (lo hi : Form d)
    (L : Nat→ParamLine d) (a b : ℚ) (ts : List Triple) : Bool :=
  OpenMathConstructionBooleanMemo.visiblesBool n lo hi (fun i => clearLine (L i)) a b ts

theorem clearedVisibles_sound {d : Nat} (n : Nat) (lo hi : Form d)
    (L : Nat→ParamLine d) (a b : ℚ) (ts : List Triple) (h : clearedVisiblesBool n lo hi L a b ts=true) :
    ts.all (fun t => decide (VisibleCheck n lo hi L a b t))=true := by
  have hh := OpenMathConstructionBooleanMemo.visibles_sound n lo hi (fun i => clearLine (L i)) a b ts h
  apply List.all_eq_true.mpr
  intro t ht
  apply decide_eq_true
  exact visible_descaling n lo hi L (fun i => multiplier (L i))
    (fun i => multiplier_positive (L i)) a b t (of_decide_eq_true ((List.all_eq_true.mp hh) t ht))

#print axioms triangle_descaling
#print axioms clearedSimple_sound
#print axioms clearedTriangles_sound
#print axioms clearedVisibles_sound
end Kobon.OpenMathConstructionRescale