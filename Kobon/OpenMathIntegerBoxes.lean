import Kobon.OpenMathConstructionBoolean

/-! Integer reflection for line forms and boxes with a common positive
denominator. Arithmetic inside the finite checker uses integers throughout;
ordinary kernel proofs transfer its result to the rational box predicates. -/
namespace Kobon.OpenMathIntegerBoxes
open Parametric OpenMathConstructionBoolean Finset
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 0

abbrev IntForm (d : ℕ) := Fin d → ℤ

def castForm {d : ℕ} (f : IntForm d) : Form d := fun i => (f i : ℚ)
def grid {d : ℕ} (D : ℤ) (f : IntForm d) : Form d := fun i => (f i : ℚ)/D

def lowerInt {d : ℕ} (lo hi f : IntForm d) : ℤ :=
  ∑ i,if 0≤f i then f i*lo i else f i*hi i
def upperInt {d : ℕ} (lo hi f : IntForm d) : ℤ :=
  ∑ i,if 0≤f i then f i*hi i else f i*lo i

theorem lower_identity {d : ℕ} (D : ℤ) (hD : D≠0) (lo hi f : IntForm d) :
    lower (grid D lo) (grid D hi) (castForm f)=(lowerInt lo hi f : ℚ)/D := by
  have hq : (D : ℚ)≠0 := by exact_mod_cast hD
  unfold lower lowerInt grid castForm
  push_cast
  simp only [div_eq_mul_inv]
  rw [sum_mul]
  apply sum_congr rfl
  intro i _
  by_cases h : 0≤f i
  · have hc : (0 : ℚ)≤(f i : ℚ) := by exact_mod_cast h
    simp only [if_pos h,if_pos hc]
    ring
  · have hc : ¬(0 : ℚ)≤(f i : ℚ) := by exact_mod_cast h
    simp only [if_neg h,if_neg hc]
    ring

theorem upper_identity {d : ℕ} (D : ℤ) (hD : D≠0) (lo hi f : IntForm d) :
    upper (grid D lo) (grid D hi) (castForm f)=(upperInt lo hi f : ℚ)/D := by
  exact lower_identity D hD hi lo f

structure IntLine (d : ℕ) where
  a : ℤ
  b : ℤ
  c : IntForm d
  deriving Inhabited

def castLine {d : ℕ} (l : IntLine d) : ParamLine d := ⟨l.a,l.b,castForm l.c⟩
def detInt {d : ℕ} (l m : IntLine d) : ℤ := l.a*m.b-l.b*m.a
def evalInt {d : ℕ} (r l m : IntLine d) : IntForm d := fun i =>
  r.a*(m.b*l.c i-l.b*m.c i)+r.b*(l.a*m.c i-m.a*l.c i)-detInt l m*r.c i
def orientedInt {d : ℕ} (r l m : IntLine d) : IntForm d := fun i =>
  detInt l m*evalInt r l m i

theorem evalInt_cast {d : ℕ} (r l m : IntLine d) :
    castForm (evalInt r l m)=evalForm (castLine r) (castLine l) (castLine m) := by
  ext i
  simp [castForm,evalInt,evalForm,castLine,scale,determinant,detInt]

theorem orientedInt_cast {d : ℕ} (r l m : IntLine d) :
    castForm (orientedInt r l m)=orientedForm (castLine r) (castLine l) (castLine m) := by
  rw [orientedForm,← evalInt_cast]
  ext i
  simp [castForm,orientedInt,castLine,scale,determinant,detInt]

def nonzeroBool {d : ℕ} (lo hi f : IntForm d) (e : Fin d) : Bool :=
  decide (0<lowerInt lo hi f) || decide (upperInt lo hi f<0) ||
    (allFin d (fun i => if i=e then true else decide (f i=0)) && decide (f e≠0))

theorem nonzero_sound {d : ℕ} (D : ℤ) (hD : 0<D) (lo hi f : IntForm d)
    (e : Fin d) (h : nonzeroBool lo hi f e=true) :
    NonzeroCert (grid D lo) (grid D hi) (castForm f) e := by
  have hq : (0 : ℚ)<D := by exact_mod_cast hD
  simp only [nonzeroBool,Bool.or_eq_true,Bool.and_eq_true,decide_eq_true_eq] at h
  rcases h with (hp|hn)|⟨hz,he⟩
  · left
    rw [lower_identity D (ne_of_gt hD)]
    exact div_pos (by exact_mod_cast hp) hq
  · right; left
    rw [upper_identity D (ne_of_gt hD)]
    exact div_neg_of_neg_of_pos (by exact_mod_cast hn) hq
  · right; right
    refine ⟨?_,?_⟩
    · intro i hie
      have hh := (allFin_true d _).mp hz i
      have hf : f i=0 := by simpa only [if_neg hie,decide_eq_true_eq] using hh
      simp [castForm,hf]
    · change (f e : ℚ)≠0
      exact_mod_cast he

def simpleBool {d : ℕ} (n : ℕ) (lo hi : IntForm d) (e : Fin d)
    (L : ℕ → IntLine d) : Bool :=
  allFin n fun i => allFin n fun j => allFin n fun k =>
    if i<j ∧ j<k then nonzeroBool lo hi (evalInt (L k) (L i) (L j)) e else true

theorem simple_sound {d : ℕ} (D : ℤ) (hD : 0<D) (n : ℕ) (lo hi : IntForm d)
    (e : Fin d) (L : ℕ → IntLine d) (h : simpleBool n lo hi e L=true) :
    SimpleCheck n (grid D lo) (grid D hi) e (fun i => castLine (L i)) := by
  intro i j k hij hjk
  have hh := (allFin_true n _).mp ((allFin_true n _).mp ((allFin_true n _).mp h i) j) k
  have hb : nonzeroBool lo hi (evalInt (L k) (L i) (L j)) e=true := by
    simpa only [simpleBool,if_pos (And.intro hij hjk)] using hh
  simpa only [evalInt_cast] using nonzero_sound D hD lo hi _ e hb

def triangleBool {d : ℕ} (n : ℕ) (lo hi : IntForm d) (L : ℕ → IntLine d)
    (t : Triple) : Bool :=
  decide (t.i<t.j) && decide (t.j<t.k) && decide (t.k<n) && allFin n fun r =>
    let f := orientedInt (L r) (L t.i) (L t.j)
    let g := orientedInt (L r) (L t.i) (L t.k)
    let h := orientedInt (L r) (L t.j) (L t.k)
    (decide (0≤lowerInt lo hi f) && decide (0≤lowerInt lo hi g) && decide (0≤lowerInt lo hi h)) ||
    (decide (upperInt lo hi f≤0) && decide (upperInt lo hi g≤0) && decide (upperInt lo hi h≤0))

theorem triangle_sound {d : ℕ} (D : ℤ) (hD : 0<D) (n : ℕ) (lo hi : IntForm d)
    (L : ℕ → IntLine d) (t : Triple) (h : triangleBool n lo hi L t=true) :
    TriangleCheck n (grid D lo) (grid D hi) (fun i => castLine (L i)) t := by
  have hq : (0 : ℚ)<D := by exact_mod_cast hD
  have hlo (f : IntForm d) (h : 0≤lowerInt lo hi f) :
      0≤lower (grid D lo) (grid D hi) (castForm f) := by
    rw [lower_identity D (ne_of_gt hD)]
    exact div_nonneg (by exact_mod_cast h) hq.le
  have hhi (f : IntForm d) (h : upperInt lo hi f≤0) :
      upper (grid D lo) (grid D hi) (castForm f)≤0 := by
    rw [upper_identity D (ne_of_gt hD)]
    exact div_nonpos_of_nonpos_of_nonneg (by exact_mod_cast h) hq.le
  simp only [triangleBool,Bool.and_eq_true,decide_eq_true_eq] at h
  rcases h with ⟨⟨⟨hti,htj⟩,htk⟩,hr⟩
  refine ⟨hti,htj,htk,?_⟩
  intro r
  have hh := (allFin_true n _).mp hr r
  simp only [Bool.or_eq_true,Bool.and_eq_true,decide_eq_true_eq] at hh
  rcases hh with ⟨⟨hf,hg⟩,hh⟩|⟨⟨hf,hg⟩,hh⟩
  · exact Or.inl ⟨by simpa only [orientedInt_cast] using hlo _ hf,
      by simpa only [orientedInt_cast] using hlo _ hg,
      by simpa only [orientedInt_cast] using hlo _ hh⟩
  · exact Or.inr ⟨by simpa only [orientedInt_cast] using hhi _ hf,
      by simpa only [orientedInt_cast] using hhi _ hg,
      by simpa only [orientedInt_cast] using hhi _ hh⟩

def trianglesBool {d : ℕ} (n : ℕ) (lo hi : IntForm d) (L : ℕ → IntLine d)
    (ts : List Triple) : Bool := ts.all (triangleBool n lo hi L)

theorem triangles_sound {d : ℕ} (D : ℤ) (hD : 0<D) (n : ℕ) (lo hi : IntForm d)
    (L : ℕ → IntLine d) (ts : List Triple) (h : trianglesBool n lo hi L ts=true) :
    ts.all (fun t => decide (TriangleCheck n (grid D lo) (grid D hi)
      (fun i => castLine (L i)) t))=true := by
  apply List.all_eq_true.mpr
  intro t ht
  apply decide_eq_true
  exact triangle_sound D hD n lo hi L t ((List.all_eq_true.mp h) t ht)

def cacheForm {d : ℕ} (f : IntForm d) : IntForm d :=
  let xs := Array.ofFn f
  fun i => xs[i.val]'(by simpa only [xs,Array.size_ofFn] using i.isLt)

@[simp] theorem cacheForm_eq {d : ℕ} (f : IntForm d) : cacheForm f=f := by
  funext i
  simp only [cacheForm,Array.getElem_ofFn]

def cacheLine {d : ℕ} (l : IntLine d) : IntLine d := ⟨l.a,l.b,cacheForm l.c⟩

@[simp] theorem cacheLine_eq {d : ℕ} (l : IntLine d) : cacheLine l=l := by
  simp only [cacheLine,cacheForm_eq]

def simpleCachedBool {d : ℕ} (n : ℕ) (lo hi : IntForm d) (e : Fin d)
    (L : ℕ → IntLine d) : Bool :=
  let ls := Array.ofFn (fun i : Fin n => cacheLine (L i))
  let Lm := fun i => if h : i<n then
    ls[i]'(by simpa only [ls,Array.size_ofFn] using h) else L i
  simpleBool n (cacheForm lo) (cacheForm hi) e Lm

theorem simpleCached_sound {d : ℕ} (D : ℤ) (hD : 0<D) (n : ℕ) (lo hi : IntForm d)
    (e : Fin d) (L : ℕ → IntLine d) (h : simpleCachedBool n lo hi e L=true) :
    SimpleCheck n (grid D lo) (grid D hi) e (fun i => castLine (L i)) := by
  have he : simpleCachedBool n lo hi e L=simpleBool n lo hi e L := by
    simp [simpleCachedBool,cacheForm_eq,cacheLine_eq,Array.getElem_ofFn]
  rw [he] at h
  exact simple_sound D hD n lo hi e L h

#print axioms lower_identity
#print axioms simple_sound
#print axioms triangle_sound
end Kobon.OpenMathIntegerBoxes
