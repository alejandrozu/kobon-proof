import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
Unconditional arithmetic of the recorded families. These are NOT unconditional
geometric existence theorems. BBL compatibility, its geometric doubling theorem,
and the Euclidean boundary reduction are separate proof obligations.
-/
namespace Kobon.Families

def q (t : Nat) : Nat := 10*2^t
def size (t : Nat) : Nat := q t+1
def triangles : Nat → Nat
  | 0 => 32
  | t+1 => triangles t+(q t)^2

theorem power_identity (t : Nat) : (2^t)^2 = (4:Nat)^t := by
  rw [← pow_mul, Nat.mul_comm t 2, pow_mul]
  norm_num

theorem triple_count (t : Nat) : 3*triangles t+4 = 100*4^t := by
  induction t with
  | zero => norm_num [triangles]
  | succ t ih =>
    simp only [triangles,q,pow_succ]
    have hp := power_identity t
    nlinarith

theorem closed_form (t : Nat) : triangles t = (100*4^t-4)/3 := by
  have h := triple_count t
  omega

theorem one_triangle_gap (t : Nat) :
    3*(triangles t+1) = size t*(size t-2) := by
  have h := triple_count t
  have hp := power_identity t
  have hpos : 0 < (2:Nat)^t := by positivity
  dsimp [size,q]
  have hsub : 10*2^t+1-2+1 = 10*2^t := by omega
  nlinarith

theorem gap_preserved (q T deficit : Int)
    (h : 3*T+deficit=q^2-1) :
    3*(T+q^2)+deficit=(2*q)^2-1 := by nlinarith

def extraSize (t : Nat) : Nat := 6*2^t+3
def extraTriangles (t : Nat) : Nat := 12*4^t+6*2^t+1

theorem extra_family_identity (t : Nat) :
    3*extraTriangles t = extraSize t*(extraSize t-3)+3 := by
  have hp := power_identity t
  simp only [extraTriangles,extraSize,Nat.add_sub_cancel]
  nlinarith

theorem samples :
    triangles 3=2132 ∧ triangles 4=8532 ∧
    triangles 5=34132 ∧ triangles 6=136532 ∧
    extraTriangles 3=817 ∧ extraTriangles 4=3169 ∧ extraTriangles 5=12481 := by
  norm_num [triangles,q,extraTriangles]

#print axioms triple_count
#print axioms one_triangle_gap
#print axioms extra_family_identity
#print axioms samples

end Kobon.Families
