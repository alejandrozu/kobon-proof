import Kobon.OpenMathConstructionBoolean

/-!
# Materialized inputs for the finite parametric Boolean checker

The outer definitions return Bool. Bounds and every line's coefficient
vector are materialized before the nested checker starts, so eta expansion
of a Form-valued helper cannot reallocate these vectors on every lookup.
The computation is extensionally equal to the original Boolean checker.
-/

namespace Kobon.OpenMathConstructionBooleanMemo
open Parametric HybridBoundary
set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- This helper returns a structure, not a function. The coefficient array
is captured by the structure's c field. -/
def materializeLine {d : Nat} (l : ParamLine d) : ParamLine d :=
  let cs := Array.ofFn l.c
  ⟨l.a,l.b,fun i => cs[i.val]'(by simpa only [cs,Array.size_ofFn] using i.isLt)⟩

theorem materializeLine_eq {d : Nat} (l : ParamLine d) : materializeLine l=l := by
  cases l
  simp [materializeLine]

theorem readForm_eq {d : Nat} (f : Form d) :
    (fun i : Fin d => (Array.ofFn f)[i.val]'(by simpa only [Array.size_ofFn] using i.isLt))=f := by
  funext i
  simp only [Array.getElem_ofFn]

theorem readLines_eq {d : Nat} (n : Nat) (L : Nat→ParamLine d) :
    (fun i : Nat => if h : i<n then
      (Array.ofFn (fun j : Fin n => materializeLine (L j)))[i]'(by simpa only [Array.size_ofFn] using h)
      else L i)=L := by
  funext i
  by_cases h : i<n
  · simp only [dif_pos h,Array.getElem_ofFn,materializeLine_eq]
  · simp only [dif_neg h]

def simpleBool {d : Nat} (n : Nat) (lo hi : Form d) (e : Fin d)
    (L : Nat→ParamLine d) : Bool :=
  let lv := Array.ofFn lo
  let hv := Array.ofFn hi
  let ls := Array.ofFn (fun i : Fin n => materializeLine (L i))
  let lm : Form d := fun i => lv[i.val]'(by simpa only [lv,Array.size_ofFn] using i.isLt)
  let hm : Form d := fun i => hv[i.val]'(by simpa only [hv,Array.size_ofFn] using i.isLt)
  let Lm : Nat→ParamLine d := fun i => if h : i<n then
    ls[i]'(by simpa only [ls,Array.size_ofFn] using h) else L i
  OpenMathConstructionBoolean.simpleBool n lm hm e Lm

theorem simpleBool_eq {d : Nat} (n : Nat) (lo hi : Form d) (e : Fin d)
    (L : Nat→ParamLine d) :
    simpleBool n lo hi e L=OpenMathConstructionBoolean.simpleBool n lo hi e L := by
  simp only [simpleBool,readForm_eq,readLines_eq]

theorem simple_sound {d : Nat} (n : Nat) (lo hi : Form d) (e : Fin d)
    (L : Nat→ParamLine d) (h : simpleBool n lo hi e L=true) :
    SimpleCheck n lo hi e L := by
  apply OpenMathConstructionBoolean.simple_sound n lo hi e L
  simpa only [simpleBool_eq] using h

def trianglesBool {d : Nat} (n : Nat) (lo hi : Form d)
    (L : Nat→ParamLine d) (ts : List Triple) : Bool :=
  let lv := Array.ofFn lo
  let hv := Array.ofFn hi
  let ls := Array.ofFn (fun i : Fin n => materializeLine (L i))
  let lm : Form d := fun i => lv[i.val]'(by simpa only [lv,Array.size_ofFn] using i.isLt)
  let hm : Form d := fun i => hv[i.val]'(by simpa only [hv,Array.size_ofFn] using i.isLt)
  let Lm : Nat→ParamLine d := fun i => if h : i<n then
    ls[i]'(by simpa only [ls,Array.size_ofFn] using h) else L i
  OpenMathConstructionBoolean.trianglesBool n lm hm Lm ts

theorem trianglesBool_eq {d : Nat} (n : Nat) (lo hi : Form d)
    (L : Nat→ParamLine d) (ts : List Triple) :
    trianglesBool n lo hi L ts=OpenMathConstructionBoolean.trianglesBool n lo hi L ts := by
  simp only [trianglesBool,readForm_eq,readLines_eq]

theorem triangles_sound {d : Nat} (n : Nat) (lo hi : Form d)
    (L : Nat→ParamLine d) (ts : List Triple)
    (h : trianglesBool n lo hi L ts=true) :
    ts.all (fun t => decide (TriangleCheck n lo hi L t))=true := by
  apply OpenMathConstructionBoolean.triangles_sound n lo hi L ts
  simpa only [trianglesBool_eq] using h

def visiblesBool {d : Nat} (n : Nat) (lo hi : Form d)
    (L : Nat→ParamLine d) (a b : ℚ) (ts : List Triple) : Bool :=
  let lv := Array.ofFn lo
  let hv := Array.ofFn hi
  let ls := Array.ofFn (fun i : Fin n => materializeLine (L i))
  let lm : Form d := fun i => lv[i.val]'(by simpa only [lv,Array.size_ofFn] using i.isLt)
  let hm : Form d := fun i => hv[i.val]'(by simpa only [hv,Array.size_ofFn] using i.isLt)
  let Lm : Nat→ParamLine d := fun i => if h : i<n then
    ls[i]'(by simpa only [ls,Array.size_ofFn] using h) else L i
  OpenMathConstructionBoolean.visiblesBool n lm hm Lm a b ts

theorem visiblesBool_eq {d : Nat} (n : Nat) (lo hi : Form d)
    (L : Nat→ParamLine d) (a b : ℚ) (ts : List Triple) :
    visiblesBool n lo hi L a b ts=OpenMathConstructionBoolean.visiblesBool n lo hi L a b ts := by
  simp only [visiblesBool,readForm_eq,readLines_eq]

theorem visibles_sound {d : Nat} (n : Nat) (lo hi : Form d)
    (L : Nat→ParamLine d) (a b : ℚ) (ts : List Triple)
    (h : visiblesBool n lo hi L a b ts=true) :
    ts.all (fun t => decide (VisibleCheck n lo hi L a b t))=true := by
  apply OpenMathConstructionBoolean.visibles_sound n lo hi L a b ts
  simpa only [visiblesBool_eq] using h

#print axioms simple_sound
#print axioms triangles_sound
#print axioms visibles_sound
end Kobon.OpenMathConstructionBooleanMemo
