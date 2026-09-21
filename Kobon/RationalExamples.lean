import Mathlib.Data.Rat.Defs
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.NormNum

/-!
Closed exact examples. The predicates are the strict same-side definition
for simple rational line arrangements. The final examples use `decide`,
so their proofs are checked by Lean's kernel, not a floating-point routine.
-/
namespace KobonExamples

structure QLine where
  slope : ℚ
  intercept : ℚ

def vertex (a b : QLine) : ℚ × ℚ :=
  let x := (b.intercept - a.intercept) / (a.slope - b.slope)
  (x, a.slope * x + a.intercept)

def side (l : QLine) (p : ℚ × ℚ) : ℚ :=
  p.2 - l.slope * p.1 - l.intercept

abbrev IsSimple {n : ℕ} (L : Fin n → QLine) : Prop :=
  (∀ i j, i ≠ j → (L i).slope ≠ (L j).slope) ∧
  (∀ i j k, i < j → j < k → side (L k) (vertex (L i) (L j)) ≠ 0)

abbrev IsTriangle {n : ℕ} (L : Fin n → QLine) (i j k : Fin n) : Prop :=
  i < j ∧ j < k ∧
  ∀ r, r ≠ i → r ≠ j → r ≠ k →
    side (L r) (vertex (L i) (L j)) * side (L r) (vertex (L j) (L k)) > 0 ∧
    side (L r) (vertex (L i) (L j)) * side (L r) (vertex (L i) (L k)) > 0

def triangleCount {n : ℕ} (L : Fin n → QLine) : ℕ :=
  ((Finset.univ : Finset (Fin n × Fin n × Fin n)).filter
    (fun t => IsTriangle L t.1 t.2.1 t.2.2)).card

def bad5 : Fin 5 → QLine := ![⟨0,0⟩,⟨1,1⟩,⟨2,4⟩,⟨3,9⟩,⟨4,16⟩]
def bad6 : Fin 6 → QLine := ![⟨0,0⟩,⟨1,1⟩,⟨2,4⟩,⟨3,9⟩,⟨4,16⟩,⟨1/2,100⟩]

def good5 : Fin 5 → QLine := ![⟨0,0⟩,⟨1,1⟩,⟨2,4⟩,⟨3,9⟩,⟨7/6,5/2⟩]
def good6 : Fin 6 → QLine := ![⟨0,0⟩,⟨1,1⟩,⟨2,4⟩,⟨3,9⟩,⟨7/6,5/2⟩,⟨28/19,-2/19⟩]
def good7 : Fin 7 → QLine := ![⟨0,0⟩,⟨1,1⟩,⟨2,4⟩,⟨3,9⟩,⟨7/6,5/2⟩,⟨28/19,-2/19⟩,⟨12/5,16⟩]

set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

theorem bad5_simple : IsSimple bad5 := by decide +kernel
theorem bad6_simple : IsSimple bad6 := by decide +kernel
theorem bad5_count : triangleCount bad5 = 3 := by decide +kernel
theorem bad6_count : triangleCount bad6 = 4 := by decide +kernel

theorem good5_simple : IsSimple good5 := by decide +kernel
theorem good6_simple : IsSimple good6 := by decide +kernel
theorem good7_simple : IsSimple good7 := by decide +kernel
theorem good5_count : triangleCount good5 = 5 := by decide +kernel
theorem good6_count : triangleCount good6 = 7 := by decide +kernel
theorem good7_count : triangleCount good7 = 10 := by decide +kernel

#print axioms bad6_count
#print axioms good7_count
#print axioms good7_simple

end KobonExamples

