import Mathlib.Data.Real.Basic
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Tactic.FieldSimp
import Mathlib.Data.List.Chain

/-!
Exact straight-line certificates.  Lines use a*x+b*y=c and may be vertical.
The real definition permits triple intersections, but the delivered witnesses
have no parallel pairs.  Weak signs allow another line through a triangle's
vertex; a line taking both strict signs at its vertices is excluded.
-/
namespace Kobon

structure Line (R : Type) where
  a : R
  b : R
  c : R
  deriving DecidableEq, Repr, Inhabited

structure Triple where
  i : Nat
  j : Nat
  k : Nat
  deriving DecidableEq, Repr, Inhabited

def det {R : Type} [CommRing R] (l m : Line R) : R := l.a*m.b-l.b*m.a

/-- Homogeneous intersection, before dividing by its nonzero last coordinate. -/
def vertex {R : Type} [CommRing R] (l m : Line R) : R × R × R :=
  (l.c*m.b-l.b*m.c, l.a*m.c-l.c*m.a, det l m)

def evalVertex {R : Type} [CommRing R] (r l m : Line R) : R :=
  let p := vertex l m
  r.a*p.1+r.b*p.2.1-r.c*p.2.2

/-- Same sign as the affine line evaluation: multiply by z instead of divide.
The two expressions differ by the strictly positive factor z^2. -/
def orientedEval {R : Type} [CommRing R] (r l m : Line R) : R :=
  evalVertex r l m * det l m

def NoParallel {R : Type} [CommRing R] (n : Nat) (L : Nat → Line R) : Prop :=
  ∀ i j : Fin n, i < j → det (L i) (L j) ≠ 0

def TrianglePredicate {R : Type} [CommRing R] [PartialOrder R]
    (n : Nat) (L : Nat → Line R) (t : Triple) : Prop :=
  t.i < t.j ∧ t.j < t.k ∧ t.k < n ∧
  evalVertex (L t.k) (L t.i) (L t.j) ≠ 0 ∧
  ∀ r : Fin n,
    (0 ≤ orientedEval (L r) (L t.i) (L t.j) ∧
     0 ≤ orientedEval (L r) (L t.i) (L t.k) ∧
     0 ≤ orientedEval (L r) (L t.j) (L t.k)) ∨
    (orientedEval (L r) (L t.i) (L t.j) ≤ 0 ∧
     orientedEval (L r) (L t.i) (L t.k) ≤ 0 ∧
     orientedEval (L r) (L t.j) (L t.k) ≤ 0)

/-- Existence of n real nonparallel lines and at least T distinct empty
nondegenerate supporting triples. This is a lower-bound predicate, not an
assumption that all maximizing arrangements are simple or nonparallel. -/
def LowerBound (n T : Nat) : Prop :=
  ∃ L : Nat → Line ℝ, NoParallel n L ∧
    ∃ ts : List Triple, ts.Nodup ∧
      (∀ t ∈ ts, TrianglePredicate n L t) ∧ T ≤ ts.length

def liftLine (l : Line ℤ) : Line ℝ := ⟨l.a,l.b,l.c⟩

@[simp] theorem det_lift (l m : Line ℤ) :
    det (liftLine l) (liftLine m) = (↑(det l m) : ℝ) := by
  simp [det,liftLine]

@[simp] theorem eval_lift (r l m : Line ℤ) :
    evalVertex (liftLine r) (liftLine l) (liftLine m) = (↑(evalVertex r l m) : ℝ) := by
  simp [evalVertex,vertex,det,liftLine]

@[simp] theorem oriented_lift (r l m : Line ℤ) :
    orientedEval (liftLine r) (liftLine l) (liftLine m) = (↑(orientedEval r l m) : ℝ) := by
  simp [orientedEval]

theorem triangle_lift (n : Nat) (L : Nat → Line ℤ) (t : Triple)
    (h : TrianglePredicate n L t) :
    TrianglePredicate n (fun i => liftLine (L i)) t := by
  rcases h with ⟨hi,hj,hk,hd,hs⟩
  refine ⟨hi,hj,hk,?_,?_⟩
  · simpa using hd
  · intro r
    simp only [oriented_lift]
    exact_mod_cast hs r

theorem noParallel_lift (n : Nat) (L : Nat → Line ℤ) (h : NoParallel n L) :
    NoParallel n (fun i => liftLine (L i)) := by
  intro i j hij
  simpa using h i j hij

/-- The polynomial sign test is the affine sign test, scaled by z^2. -/
theorem orientedEval_affine (r l m : Line ℝ) (h : det l m ≠ 0) :
    orientedEval r l m =
      (r.a*((vertex l m).1 / det l m) +
       r.b*((vertex l m).2.1 / det l m) - r.c) * (det l m)^2 := by
  unfold orientedEval evalVertex
  dsimp [vertex]
  field_simp

instance (n : Nat) (L : Nat → Line ℤ) : Decidable (NoParallel n L) := by
  unfold NoParallel
  infer_instance

instance (n : Nat) (L : Nat → Line ℤ) (t : Triple) :
    Decidable (TrianglePredicate n L t) := by
  unfold TrianglePredicate
  infer_instance

def linesAt (ls : Array (Line ℤ)) (i : Nat) : Line ℤ := ls[i]!

def tripleKey (n : Nat) (t : Triple) : Nat := (t.i*n+t.j)*n+t.k

def Increasing (n : Nat) (ts : List Triple) : Prop :=
  (ts.map (tripleKey n)).IsChain (· < ·)

instance (n : Nat) (ts : List Triple) : Decidable (Increasing n ts) := by
  unfold Increasing
  infer_instance

theorem increasing_nodup (n : Nat) (ts : List Triple) (h : Increasing n ts) : ts.Nodup := by
  have hp : ts.Pairwise (fun a b => tripleKey n a < tripleKey n b) :=
    List.pairwise_map.mp (List.isChain_iff_pairwise.mp h)
  apply hp.imp
  intro a b hab heq
  subst b
  exact (Nat.lt_irrefl _) hab

def validate (ls : Array (Line ℤ)) (ts : List Triple) (T : Nat) : Bool :=
  decide (NoParallel ls.size (linesAt ls)) && decide (Increasing ls.size ts) &&
  ts.all (fun t => decide (TrianglePredicate ls.size (linesAt ls) t)) &&
  decide (T ≤ ts.length)

theorem validate_sound (ls : Array (Line ℤ)) (ts : List Triple) (T : Nat)
    (h : validate ls ts T = true) : LowerBound ls.size T := by
  simp only [validate,Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true] at h
  rcases h with ⟨⟨⟨hp,hn⟩,ht⟩,hc⟩
  refine ⟨fun i => liftLine (linesAt ls i),noParallel_lift _ _ hp,ts,
    increasing_nodup _ _ hn,?_,hc⟩
  intro t hmem
  exact triangle_lift _ _ _ (ht t hmem)

#print axioms validate_sound
#print axioms orientedEval_affine

end Kobon
