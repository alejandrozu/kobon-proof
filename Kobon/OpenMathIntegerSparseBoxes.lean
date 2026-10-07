import Kobon.OpenMathIntegerBoxes
import Mathlib.Data.Finset.Sort

/-! Sparse integer interval bounds. Finite supports are explicit data, and
ordinary kernel proofs use sum_subset to justify omitting every other coordinate.
The sparse reflection remains sound to the existing rational-box predicates.
-/
namespace Kobon.OpenMathIntegerSparseBoxes
open OpenMathIntegerBoxes OpenMathConstructionBoolean Parametric Finset
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1000000

def Supported {d : Nat} (S : Finset (Fin d)) (f : IntForm d) : Prop :=
  ∀ i, i∉S → f i=0

def lowerSparse {d : Nat} (lo hi f : IntForm d) (S : Finset (Fin d)) : Int :=
  ∑ i∈S, if 0 ≤ f i then f i*lo i else f i*hi i

def upperSparse {d : Nat} (lo hi f : IntForm d) (S : Finset (Fin d)) : Int :=
  ∑ i∈S, if 0 ≤ f i then f i*hi i else f i*lo i

theorem lowerSparse_eq {d : Nat} (lo hi f : IntForm d) (S : Finset (Fin d))
    (h : Supported S f) : lowerSparse lo hi f S=lowerInt lo hi f := by
  unfold lowerSparse lowerInt
  apply Finset.sum_subset (Finset.subset_univ S)
  intro i _ hi
  simp [h i hi]

theorem upperSparse_eq {d : Nat} (lo hi f : IntForm d) (S : Finset (Fin d))
    (h : Supported S f) : upperSparse lo hi f S=upperInt lo hi f :=
  lowerSparse_eq hi lo f S h

structure SingleLine (d : Nat) where
  a : Int
  b : Int
  coefficient : Int
  coordinate : Fin d

def intLine {d : Nat} (l : SingleLine d) : IntLine d :=
  ⟨l.a,l.b,fun i => if i=l.coordinate then l.coefficient else 0⟩

def lineSupport {d : Nat} (r l m : SingleLine d) : Finset (Fin d) :=
  {r.coordinate,l.coordinate,m.coordinate}

theorem eval_supported {d : Nat} (r l m : SingleLine d) :
    Supported (lineSupport r l m) (evalInt (intLine r) (intLine l) (intLine m)) := by
  intro i hi
  have hr : i≠r.coordinate := by intro h; apply hi; simp [lineSupport,h]
  have hl : i≠l.coordinate := by intro h; apply hi; simp [lineSupport,h]
  have hm : i≠m.coordinate := by intro h; apply hi; simp [lineSupport,h]
  simp [evalInt,intLine,hr,hl,hm]

theorem oriented_supported {d : Nat} (r l m : SingleLine d) :
    Supported (lineSupport r l m) (orientedInt (intLine r) (intLine l) (intLine m)) := by
  intro i hi
  simp only [orientedInt,eval_supported r l m i hi,mul_zero]

theorem support_card_le_three {d : Nat} (r l m : SingleLine d) :
    (lineSupport r l m).card ≤ 3 := by
  unfold lineSupport
  calc
    _ ≤ ({l.coordinate,m.coordinate} : Finset (Fin d)).card+1 := card_insert_le _ _
    _ ≤ ({m.coordinate} : Finset (Fin d)).card+1+1 := by have := card_insert_le l.coordinate ({m.coordinate} : Finset (Fin d)); omega
    _ = 3 := by simp

def nonzeroSparseBool {d : Nat} (lo hi f : IntForm d) (S : Finset (Fin d))
    (e : Fin d) : Bool :=
  decide (0<lowerSparse lo hi f S) || decide (upperSparse lo hi f S<0) ||
    ((S.sort (· ≤ ·)).all (fun i => if i=e then true else decide (f i=0)) && decide (f e≠0))

theorem nonzeroSparse_to_bool {d : Nat} (lo hi f : IntForm d) (S : Finset (Fin d))
    (e : Fin d) (hs : Supported S f) (h : nonzeroSparseBool lo hi f S e=true) :
    OpenMathIntegerBoxes.nonzeroBool lo hi f e=true := by
  simp only [nonzeroSparseBool,Bool.or_eq_true,Bool.and_eq_true,decide_eq_true_eq] at h
  simp only [OpenMathIntegerBoxes.nonzeroBool,Bool.or_eq_true,Bool.and_eq_true,decide_eq_true_eq]
  rcases h with (hp|hn)|⟨hz,he⟩
  · left; left
    simpa only [lowerSparse_eq lo hi f S hs] using hp
  · left; right
    simpa only [upperSparse_eq lo hi f S hs] using hn
  · right
    refine ⟨(allFin_true d _).mpr ?_,he⟩
    intro i
    by_cases hie : i=e
    · simp [hie]
    · have hf : f i=0 := by
        by_cases hi : i∈S
        · have hh := (List.all_eq_true.mp hz) i (by simpa only [Finset.mem_sort] using hi)
          simpa only [if_neg hie,decide_eq_true_eq] using hh
        · exact hs i hi
      simp [hie,hf]

theorem nonzeroSparse_sound {d : Nat} (D : Int) (hD : 0<D)
    (lo hi f : IntForm d) (S : Finset (Fin d)) (e : Fin d)
    (hs : Supported S f) (h : nonzeroSparseBool lo hi f S e=true) :
    NonzeroCert (grid D lo) (grid D hi) (castForm f) e :=
  nonzero_sound D hD lo hi f e (nonzeroSparse_to_bool lo hi f S e hs h)

def simpleSparseBool {d : Nat} (n : Nat) (lo hi : IntForm d) (e : Fin d)
    (L : Nat → SingleLine d) : Bool :=
  allFin n fun i => allFin n fun j => allFin n fun k =>
    if i<j ∧ j<k then
      nonzeroSparseBool lo hi (evalInt (intLine (L k)) (intLine (L i)) (intLine (L j)))
        (lineSupport (L k) (L i) (L j)) e
    else true

theorem simpleSparse_sound {d : Nat} (D : Int) (hD : 0<D) (n : Nat)
    (lo hi : IntForm d) (e : Fin d) (L : Nat → SingleLine d)
    (h : simpleSparseBool n lo hi e L=true) :
    SimpleCheck n (grid D lo) (grid D hi) e (fun i => castLine (intLine (L i))) := by
  apply simple_sound D hD n lo hi e (fun i => intLine (L i))
  apply (allFin_true n _).mpr
  intro i
  apply (allFin_true n _).mpr
  intro j
  apply (allFin_true n _).mpr
  intro k
  have hh := (allFin_true n _).mp ((allFin_true n _).mp ((allFin_true n _).mp h i) j) k
  by_cases ho : i<j ∧ j<k
  · have hn : nonzeroSparseBool lo hi
        (evalInt (intLine (L k)) (intLine (L i)) (intLine (L j)))
        (lineSupport (L k) (L i) (L j)) e=true := by
      simpa only [simpleSparseBool,if_pos ho] using hh
    simp only [OpenMathIntegerBoxes.simpleBool,if_pos ho]
    exact nonzeroSparse_to_bool lo hi _ _ e (eval_supported _ _ _) hn
  · simp only [OpenMathIntegerBoxes.simpleBool,if_neg ho]

#print axioms lowerSparse_eq
#print axioms nonzeroSparse_sound
#print axioms simpleSparse_sound
end Kobon.OpenMathIntegerSparseBoxes
