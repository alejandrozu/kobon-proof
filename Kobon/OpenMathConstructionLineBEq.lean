import Kobon.OpenMathConstructionLineEquality
import Kobon.OpenMathConstructionBooleanMemo
namespace Kobon.OpenMathConstructionLineEquality
open Parametric OpenMathConstructionBoolean
set_option autoImplicit false
set_option maxHeartbeats 0

def lineBEqBool {d : Nat} (l m : ParamLine d) : Bool :=
  (l.a==m.a) && (l.b==m.b) && allFin d (fun i => l.c i==m.c i)

theorem lineBEq_sound {d : Nat} (l m : ParamLine d) (h : lineBEqBool l m=true) : l=m := by
  simp only [lineBEqBool,Bool.and_eq_true,beq_iff_eq] at h
  apply paramLine_ext l m h.1.1 h.1.2
  funext i
  exact beq_iff_eq.mp ((allFin_true d _).mp h.2 i)

def formsBEqBool {d : Nat} (f g : Form d) : Bool := allFin d (fun i => f i==g i)

theorem formsBEq_sound {d : Nat} (f g : Form d) (h : formsBEqBool f g=true) : f=g := by
  funext i
  exact beq_iff_eq.mp ((allFin_true d _).mp h i)


def memoLineMapBEqBool {d : Nat} (n : Nat) (L M : Nat→ParamLine d) : Bool :=
  let ls := Array.ofFn (fun i : Fin n => OpenMathConstructionBooleanMemo.materializeLine (L i))
  let ms := Array.ofFn (fun i : Fin n => OpenMathConstructionBooleanMemo.materializeLine (M i))
  allFin n fun i =>
    lineBEqBool (ls[i.val]'(by simpa only [ls,Array.size_ofFn] using i.isLt))
      (ms[i.val]'(by simpa only [ms,Array.size_ofFn] using i.isLt))

theorem memoLineMapBEq_eq {d : Nat} (n : Nat) (L M : Nat→ParamLine d) :
    memoLineMapBEqBool n L M=allFin n (fun i => lineBEqBool (L i) (M i)) := by
  simp only [memoLineMapBEqBool,Array.getElem_ofFn,OpenMathConstructionBooleanMemo.materializeLine_eq]

theorem memoLineMapBEq_sound {d : Nat} (n : Nat) (L M : Nat→ParamLine d)
    (h : memoLineMapBEqBool n L M=true) (i : Fin n) : L i=M i := by
  rw [memoLineMapBEq_eq] at h
  exact lineBEq_sound (L i) (M i) ((allFin_true n _).mp h i)
#print axioms lineBEq_sound
#print axioms memoLineMapBEq_sound
end Kobon.OpenMathConstructionLineEquality

