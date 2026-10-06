import Kobon.OpenMathConstructionBoolean
namespace Kobon.OpenMathConstructionLineEquality
open Parametric OpenMathConstructionBoolean
set_option autoImplicit false
set_option maxHeartbeats 0

def lineEqualityBool {d : Nat} (l m : ParamLine d) : Bool :=
  decide (l.a=m.a) && decide (l.b=m.b) && allFin d (fun i => decide (l.c i=m.c i))

theorem paramLine_ext {d : Nat} (l m : ParamLine d)
    (ha : l.a=m.a) (hb : l.b=m.b) (hc : l.c=m.c) : l=m := by
  cases l; cases m
  dsimp only at ha hb hc
  cases ha; cases hb; cases hc
  rfl

theorem lineEquality_sound {d : Nat} (l m : ParamLine d) (h : lineEqualityBool l m=true) : l=m := by
  simp only [lineEqualityBool,Bool.and_eq_true,decide_eq_true_eq] at h
  apply paramLine_ext l m h.1.1 h.1.2
  funext i
  exact of_decide_eq_true ((allFin_true d _).mp h.2 i)

def lineMapMatchesBool {d : Nat} (n : Nat) (L M : Nat→ParamLine d) : Bool :=
  allFin n (fun i => lineEqualityBool (L i) (M i))

theorem lineMapMatches_sound {d : Nat} (n : Nat) (L M : Nat→ParamLine d)
    (h : lineMapMatchesBool n L M=true) (i : Fin n) : L i=M i :=
  lineEquality_sound (L i) (M i) ((allFin_true n _).mp h i)

def formsEqualBool {d : Nat} (f g : Form d) : Bool := allFin d (fun i => decide (f i=g i))

theorem formsEqual_sound {d : Nat} (f g : Form d) (h : formsEqualBool f g=true) : f=g := by
  funext i
  exact of_decide_eq_true ((allFin_true d _).mp h i)

theorem simpleCheck_congr {d : Nat} (n : Nat) (lo hi : Form d) (e : Fin d)
    (L M : Nat→ParamLine d) (he : ∀ i : Fin n, L i=M i)
    (h : SimpleCheck n lo hi e L) : SimpleCheck n lo hi e M := by
  intro i j k hij hjk
  have hh := h i j k hij hjk
  rwa [he i,he j,he k] at hh

theorem triangleCheck_congr {d : Nat} (n : Nat) (lo hi : Form d)
    (L M : Nat→ParamLine d) (he : ∀ i : Fin n, L i=M i) (t : Triple)
    (h : TriangleCheck n lo hi L t) : TriangleCheck n lo hi M t := by
  obtain ⟨hi,hj,hk,hr⟩ := h
  have hii : t.i<n := by omega
  have hjj : t.j<n := by omega
  refine ⟨hi,hj,hk,?_⟩
  intro r
  have hh := hr r
  rw [he r,he ⟨t.i,hii⟩,he ⟨t.j,hjj⟩,he ⟨t.k,hk⟩] at hh
  exact hh

#print axioms lineMapMatches_sound
#print axioms triangleCheck_congr
end Kobon.OpenMathConstructionLineEquality
