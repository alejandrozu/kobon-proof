import Kobon.OpenMathConstructionBooleanMemo

/-! Exact sparse interval reflection.  Each vertex form is supported on
the union of the three line coefficient supports.  Computing both bounds
in one sparse sum avoids repeated arithmetic on zero coefficients; the
soundness proofs establish equality to the original dense rational boxes. -/
namespace Kobon.OpenMathSparseBoxes
open Parametric OpenMathConstructionBoolean Finset
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1000000

def coefficientSupport {d : Nat} (l : ParamLine d) : Finset (Fin d) :=
  univ.filter (fun i => l.c i≠0)

def tripleSupport {d : Nat} (r l m : ParamLine d) : Finset (Fin d) :=
  coefficientSupport r∪coefficientSupport l∪coefficientSupport m

theorem evalForm_zero_outside {d : Nat} (r l m : ParamLine d) (i : Fin d)
    (h : i∉tripleSupport r l m) : evalForm r l m i=0 := by
  have hz : (r.c i=0 ∧ l.c i=0) ∧ m.c i=0 := by
    simpa only [tripleSupport,coefficientSupport,mem_union,mem_filter,
      mem_univ,true_and,not_or,not_not] using h
  simp [evalForm,scale,hz.1.1,hz.1.2,hz.2]

theorem orientedForm_zero_outside {d : Nat} (r l m : ParamLine d) (i : Fin d)
    (h : i∉tripleSupport r l m) : orientedForm r l m i=0 := by
  simp only [orientedForm,scale,evalForm_zero_outside r l m i h,mul_zero]

def bounds {d : Nat} (lo hi f : Form d) (S : Finset (Fin d)) : ℚ×ℚ :=
  ∑ i∈S, let c:=f i
    (if 0≤c then c*lo i else c*hi i,
     if 0≤c then c*hi i else c*lo i)

theorem bounds_exact {d : Nat} (lo hi f : Form d) (S : Finset (Fin d))
    (hz : ∀ i∉S, f i=0) : bounds lo hi f S=(lower lo hi f,upper lo hi f) := by
  classical
  apply Prod.ext
  · simp only [bounds,Prod.fst_sum,lower]
    apply sum_subset (subset_univ S)
    intro i hi hni
    simp [hz i hni]
  · simp only [bounds,Prod.snd_sum,upper]
    apply sum_subset (subset_univ S)
    intro i hi hni
    simp [hz i hni]

def nonzeroBool {d : Nat} (lo hi f : Form d) (e : Fin d)
    (S : Finset (Fin d)) : Bool :=
  let b := bounds lo hi f S
  decide (0<b.1) || decide (b.2<0) ||
    (decide (∀ i : Fin d, i∈S → i≠e → f i=0) && decide (f e≠0))

theorem nonzero_sound {d : Nat} (lo hi f : Form d) (e : Fin d)
    (S : Finset (Fin d)) (hz : ∀ i∉S, f i=0)
    (h : nonzeroBool lo hi f e S=true) : NonzeroCert lo hi f e := by
  rw [nonzeroBool,bounds_exact lo hi f S hz] at h
  simp only [Bool.or_eq_true,Bool.and_eq_true,decide_eq_true_eq] at h
  rcases h with (hp|hn)|⟨hS,he⟩
  · exact Or.inl hp
  · exact Or.inr (Or.inl hn)
  · refine Or.inr (Or.inr ⟨?_,he⟩)
    intro i hie
    by_cases hiS : i∈S
    · exact hS i hiS hie
    · exact hz i hiS

def simpleBool {d : Nat} (n : Nat) (lo hi : Form d) (e : Fin d)
    (L : Nat→ParamLine d) : Bool :=
  allFin n fun i => allFin n fun j => allFin n fun k =>
    if i<j ∧ j<k then
      nonzeroBool lo hi (evalForm (L k) (L i) (L j)) e (tripleSupport (L k) (L i) (L j))
    else true

theorem simple_sound {d : Nat} (n : Nat) (lo hi : Form d) (e : Fin d)
    (L : Nat→ParamLine d) (h : simpleBool n lo hi e L=true) :
    SimpleCheck n lo hi e L := by
  intro i j k hij hjk
  have h1 := (allFin_true n _).mp h i
  have h2 := (allFin_true n _).mp h1 j
  have h3 := (allFin_true n _).mp h2 k
  have hik : i<j ∧ j<k := ⟨hij,hjk⟩
  apply nonzero_sound lo hi _ e (tripleSupport (L k) (L i) (L j))
    (evalForm_zero_outside (L k) (L i) (L j))
  simpa only [simpleBool,if_pos hik] using h3

def triangleBool {d : Nat} (n : Nat) (lo hi : Form d)
    (L : Nat→ParamLine d) (t : Triple) : Bool :=
  decide (t.i<t.j) && decide (t.j<t.k) && decide (t.k<n) &&
    allFin n fun r =>
      let bf := bounds lo hi (orientedForm (L r) (L t.i) (L t.j))
        (tripleSupport (L r) (L t.i) (L t.j))
      let bg := bounds lo hi (orientedForm (L r) (L t.i) (L t.k))
        (tripleSupport (L r) (L t.i) (L t.k))
      let bh := bounds lo hi (orientedForm (L r) (L t.j) (L t.k))
        (tripleSupport (L r) (L t.j) (L t.k))
      (decide (0≤bf.1) && decide (0≤bg.1) && decide (0≤bh.1)) ||
      (decide (bf.2≤0) && decide (bg.2≤0) && decide (bh.2≤0))

theorem triangle_sound {d : Nat} (n : Nat) (lo hi : Form d)
    (L : Nat→ParamLine d) (t : Triple) (h : triangleBool n lo hi L t=true) :
    TriangleCheck n lo hi L t := by
  simp only [triangleBool,Bool.and_eq_true,decide_eq_true_eq] at h
  rcases h with ⟨⟨⟨hti,htj⟩,hk⟩,hr⟩
  refine ⟨hti,htj,hk,?_⟩
  intro r
  have hh := (allFin_true n _).mp hr r
  rw [bounds_exact lo hi _ _ (orientedForm_zero_outside (L r) (L t.i) (L t.j)),
    bounds_exact lo hi _ _ (orientedForm_zero_outside (L r) (L t.i) (L t.k)),
    bounds_exact lo hi _ _ (orientedForm_zero_outside (L r) (L t.j) (L t.k))] at hh
  simpa only [Bool.or_eq_true,Bool.and_eq_true,decide_eq_true_eq,and_assoc] using hh

def trianglesBool {d : Nat} (n : Nat) (lo hi : Form d)
    (L : Nat→ParamLine d) (ts : List Triple) : Bool := ts.all (triangleBool n lo hi L)

theorem triangles_sound {d : Nat} (n : Nat) (lo hi : Form d)
    (L : Nat→ParamLine d) (ts : List Triple) (h : trianglesBool n lo hi L ts=true) :
    ts.all (fun t => decide (TriangleCheck n lo hi L t))=true := by
  apply List.all_eq_true.mpr
  intro t ht
  apply decide_eq_true
  exact triangle_sound n lo hi L t ((List.all_eq_true.mp h) t ht)

def simpleMemoBool {d : Nat} (n : Nat) (lo hi : Form d) (e : Fin d)
    (L : Nat→ParamLine d) : Bool :=
  let lv := Array.ofFn lo
  let hv := Array.ofFn hi
  let ls := Array.ofFn (fun i : Fin n => OpenMathConstructionBooleanMemo.materializeLine (L i))
  let lm : Form d := fun i => lv[i.val]'(by simpa only [lv,Array.size_ofFn] using i.isLt)
  let hm : Form d := fun i => hv[i.val]'(by simpa only [hv,Array.size_ofFn] using i.isLt)
  let Lm : Nat→ParamLine d := fun i => if h : i<n then
    ls[i]'(by simpa only [ls,Array.size_ofFn] using h) else L i
  simpleBool n lm hm e Lm

theorem simpleMemoBool_eq {d : Nat} (n : Nat) (lo hi : Form d) (e : Fin d)
    (L : Nat→ParamLine d) : simpleMemoBool n lo hi e L=simpleBool n lo hi e L := by
  simp only [simpleMemoBool,OpenMathConstructionBooleanMemo.readForm_eq,
    OpenMathConstructionBooleanMemo.readLines_eq]

theorem simpleMemo_sound {d : Nat} (n : Nat) (lo hi : Form d) (e : Fin d)
    (L : Nat→ParamLine d) (h : simpleMemoBool n lo hi e L=true) :
    SimpleCheck n lo hi e L := by
  exact simple_sound n lo hi e L (by simpa only [simpleMemoBool_eq] using h)

def trianglesMemoBool {d : Nat} (n : Nat) (lo hi : Form d)
    (L : Nat→ParamLine d) (ts : List Triple) : Bool :=
  let lv := Array.ofFn lo
  let hv := Array.ofFn hi
  let ls := Array.ofFn (fun i : Fin n => OpenMathConstructionBooleanMemo.materializeLine (L i))
  let lm : Form d := fun i => lv[i.val]'(by simpa only [lv,Array.size_ofFn] using i.isLt)
  let hm : Form d := fun i => hv[i.val]'(by simpa only [hv,Array.size_ofFn] using i.isLt)
  let Lm : Nat→ParamLine d := fun i => if h : i<n then
    ls[i]'(by simpa only [ls,Array.size_ofFn] using h) else L i
  trianglesBool n lm hm Lm ts

theorem trianglesMemoBool_eq {d : Nat} (n : Nat) (lo hi : Form d)
    (L : Nat→ParamLine d) (ts : List Triple) :
    trianglesMemoBool n lo hi L ts=trianglesBool n lo hi L ts := by
  simp only [trianglesMemoBool,OpenMathConstructionBooleanMemo.readForm_eq,
    OpenMathConstructionBooleanMemo.readLines_eq]

theorem trianglesMemo_sound {d : Nat} (n : Nat) (lo hi : Form d)
    (L : Nat→ParamLine d) (ts : List Triple) (h : trianglesMemoBool n lo hi L ts=true) :
    ts.all (fun t => decide (TriangleCheck n lo hi L t))=true := by
  exact triangles_sound n lo hi L ts (by simpa only [trianglesMemoBool_eq] using h)

#print axioms bounds_exact
#print axioms simple_sound
#print axioms triangles_sound
#print axioms simpleMemo_sound
#print axioms trianglesMemo_sound
end Kobon.OpenMathSparseBoxes
