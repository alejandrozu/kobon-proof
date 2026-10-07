import Kobon.ParametricCached
import Kobon.HybridBoundary
import Mathlib.Data.List.FinRange

/-!
Executable finite reflection for parametric line certificates.

Only equality of an explicitly computed Boolean to `true` is submitted to
native evaluation. The soundness bridges below are ordinary kernel proofs.
This avoids specializing enormous quantified Decidable instances in the
statement passed to native_decide. Form coefficients are materialized once
before each interval calculation. No geometric premise is introduced.
-/
namespace Kobon.OpenMathConstructionBoolean
open Parametric HybridBoundary
set_option autoImplicit false
set_option maxHeartbeats 1000000

def allFin (n : Nat) (p : Fin n → Bool) : Bool := (List.finRange n).all p

theorem allFin_true (n : Nat) (p : Fin n → Bool) :
    allFin n p=true ↔ ∀ i, p i=true := by
  simp [allFin,List.all_eq_true]

def directionsBool {d : Nat} (n : Nat) (L : Nat→ParamLine d) : Bool :=
  allFin n fun i => allFin n fun j =>
    if i<j then decide (determinant (L i) (L j)≠0) else true

theorem directions_sound {d : Nat} (n : Nat) (L : Nat→ParamLine d)
    (h : directionsBool n L=true) : DirectionCheck n L := by
  intro i j hij
  have h1 := (allFin_true n _).mp h i
  have h2 := (allFin_true n _).mp h1 j
  simpa only [if_pos hij,decide_eq_true_eq] using h2

def nonzeroBool {d : Nat} (lo hi f : Form d) (e : Fin d) : Bool :=
  decide (0<lower lo hi f) || decide (upper lo hi f<0) ||
    (allFin d (fun i => if i=e then true else decide (f i=0)) && decide (f e≠0))

theorem nonzero_sound {d : Nat} (lo hi f : Form d) (e : Fin d)
    (h : nonzeroBool lo hi f e=true) : NonzeroCert lo hi f e := by
  simp only [nonzeroBool,Bool.or_eq_true,Bool.and_eq_true,decide_eq_true_eq] at h
  rcases h with (hp | hn) | ⟨hz,he⟩
  · exact Or.inl hp
  · exact Or.inr (Or.inl hn)
  · refine Or.inr (Or.inr ⟨?_,he⟩)
    intro i hie
    have hh := (allFin_true d _).mp hz i
    simpa only [if_neg hie,decide_eq_true_eq] using hh

def simpleBool {d : Nat} (n : Nat) (lo hi : Form d) (e : Fin d)
    (L : Nat→ParamLine d) : Bool :=
  allFin n fun i => allFin n fun j => allFin n fun k =>
    if i<j ∧ j<k then
      let xs := Array.ofFn (evalForm (L k) (L i) (L j))
      let f : Form d := fun z => xs[z.val]'(by simpa only [xs,Array.size_ofFn] using z.isLt)
      nonzeroBool lo hi f e
    else true

theorem simple_sound {d : Nat} (n : Nat) (lo hi : Form d) (e : Fin d)
    (L : Nat→ParamLine d) (h : simpleBool n lo hi e L=true) :
    SimpleCheck n lo hi e L := by
  intro i j k hij hjk
  have h1 := (allFin_true n _).mp h i
  have h2 := (allFin_true n _).mp h1 j
  have h3 := (allFin_true n _).mp h2 k
  have hik : i<j ∧ j<k := ⟨hij,hjk⟩
  have hh : nonzeroBool lo hi
      (ParametricCached.cache (evalForm (L k) (L i) (L j))) e=true := by
    simpa only [if_pos hik,ParametricCached.cache] using h3
  simpa only [ParametricCached.cache_eq] using nonzero_sound lo hi _ e hh

def triangleBool {d : Nat} (n : Nat) (lo hi : Form d)
    (L : Nat→ParamLine d) (t : Triple) : Bool :=
  decide (t.i<t.j) && decide (t.j<t.k) && decide (t.k<n) &&
    allFin n fun r =>
      let xf := Array.ofFn (orientedForm (L r) (L t.i) (L t.j))
      let f : Form d := fun z => xf[z.val]'(by simpa only [xf,Array.size_ofFn] using z.isLt)
      let xg := Array.ofFn (orientedForm (L r) (L t.i) (L t.k))
      let g : Form d := fun z => xg[z.val]'(by simpa only [xg,Array.size_ofFn] using z.isLt)
      let xh := Array.ofFn (orientedForm (L r) (L t.j) (L t.k))
      let h : Form d := fun z => xh[z.val]'(by simpa only [xh,Array.size_ofFn] using z.isLt)
      (decide (0≤lower lo hi f) && decide (0≤lower lo hi g) && decide (0≤lower lo hi h)) ||
      (decide (upper lo hi f≤0) && decide (upper lo hi g≤0) && decide (upper lo hi h≤0))

theorem triangle_sound {d : Nat} (n : Nat) (lo hi : Form d)
    (L : Nat→ParamLine d) (t : Triple) (h : triangleBool n lo hi L t=true) :
    TriangleCheck n lo hi L t := by
  simp only [triangleBool,Bool.and_eq_true,decide_eq_true_eq] at h
  rcases h with ⟨⟨⟨hi,hj⟩,hk⟩,hr⟩
  refine ⟨hi,hj,hk,?_⟩
  intro r
  have hh := (allFin_true n _).mp hr r
  simpa only [Array.getElem_ofFn,Bool.or_eq_true,Bool.and_eq_true,
    decide_eq_true_eq,and_assoc] using hh

def trianglesBool {d : Nat} (n : Nat) (lo hi : Form d)
    (L : Nat→ParamLine d) (ts : List Triple) : Bool :=
  ts.all (triangleBool n lo hi L)

theorem triangles_sound {d : Nat} (n : Nat) (lo hi : Form d)
    (L : Nat→ParamLine d) (ts : List Triple) (h : trianglesBool n lo hi L ts=true) :
    ts.all (fun t => decide (TriangleCheck n lo hi L t))=true := by
  apply List.all_eq_true.mpr
  intro t ht
  apply decide_eq_true
  exact triangle_sound n lo hi L t ((List.all_eq_true.mp h) t ht)

def visibleBool {d : Nat} (n : Nat) (lo hi : Form d)
    (L : Nat→ParamLine d) (a b : ℚ) (t : Triple) : Bool :=
  decide (t.i<t.j) && decide (t.j<n) && decide (t.k=n) &&
    allFin n fun r =>
      let xf := Array.ofFn (orientedForm (L r) (L t.i) (L t.j))
      let f : Form d := fun z => xf[z.val]'(by simpa only [xf,Array.size_ofFn] using z.isLt)
      let di := derivativeNumerator (L r) (L t.i) a b
      let dj := derivativeNumerator (L r) (L t.j) a b
      (decide (0≤lower lo hi f) && decide (0≤di) && decide (0≤dj)) ||
      (decide (upper lo hi f≤0) && decide (di≤0) && decide (dj≤0))

theorem visible_sound {d : Nat} (n : Nat) (lo hi : Form d)
    (L : Nat→ParamLine d) (a b : ℚ) (t : Triple) (h : visibleBool n lo hi L a b t=true) :
    VisibleCheck n lo hi L a b t := by
  simp only [visibleBool,Bool.and_eq_true,decide_eq_true_eq] at h
  rcases h with ⟨⟨⟨hi,hj⟩,hk⟩,hr⟩
  refine ⟨hi,hj,hk,?_⟩
  intro r
  have hh := (allFin_true n _).mp hr r
  simpa only [Array.getElem_ofFn,Bool.or_eq_true,Bool.and_eq_true,
    decide_eq_true_eq,and_assoc] using hh

def visiblesBool {d : Nat} (n : Nat) (lo hi : Form d)
    (L : Nat→ParamLine d) (a b : ℚ) (ts : List Triple) : Bool :=
  ts.all (visibleBool n lo hi L a b)

theorem visibles_sound {d : Nat} (n : Nat) (lo hi : Form d)
    (L : Nat→ParamLine d) (a b : ℚ) (ts : List Triple)
    (h : visiblesBool n lo hi L a b ts=true) :
    ts.all (fun t => decide (VisibleCheck n lo hi L a b t))=true := by
  apply List.all_eq_true.mpr
  intro t ht
  apply decide_eq_true
  exact visible_sound n lo hi L a b t ((List.all_eq_true.mp h) t ht)

def admissibleBool {d : Nat} (n : Nat) (L : Nat→ParamLine d) (a b : ℚ) : Bool :=
  allFin n fun i => decide ((L i).a*b-(L i).b*a≠0)

theorem admissible_sound {d : Nat} (n : Nat) (L : Nat→ParamLine d) (a b : ℚ)
    (h : admissibleBool n L a b=true) : AdmissibleCheck n L a b := by
  intro i
  exact of_decide_eq_true ((allFin_true n _).mp h i)

#print axioms directions_sound
#print axioms simple_sound
#print axioms triangle_sound
#print axioms visible_sound
end Kobon.OpenMathConstructionBoolean