import Kobon.Geometry

/-! Simplicity is an additional property of a witness, not a restriction on
the classical Kobon problem.  This file checks it separately. -/
namespace Kobon

def NoConcurrent {R : Type} [CommRing R] (n : Nat) (L : Nat → Line R) : Prop :=
  ∀ i j k : Fin n, i < j → j < k → evalVertex (L k) (L i) (L j) ≠ 0

instance (n : Nat) (L : Nat → Line ℤ) : Decidable (NoConcurrent n L) := by
  unfold NoConcurrent
  infer_instance

theorem noConcurrent_lift (n : Nat) (L : Nat → Line ℤ) (h : NoConcurrent n L) :
    NoConcurrent n (fun i => liftLine (L i)) := by
  intro i j k hij hjk
  simpa using h i j k hij hjk

def SimpleLowerBound (n T : Nat) : Prop :=
  ∃ L : Nat → Line ℝ, NoParallel n L ∧ NoConcurrent n L ∧
    ∃ ts : List Triple, ts.Nodup ∧
      (∀ t ∈ ts, TrianglePredicate n L t) ∧ T ≤ ts.length

theorem SimpleLowerBound.classical {n T : Nat} (h : SimpleLowerBound n T) :
    LowerBound n T := by
  rcases h with ⟨L,hp,_,ts,hn,ht,hc⟩
  exact ⟨L,hp,ts,hn,ht,hc⟩

theorem LowerBound.mono {n T U : Nat} (h : LowerBound n T) (hU : U ≤ T) :
    LowerBound n U := by
  rcases h with ⟨L,hp,ts,hn,ht,hc⟩
  exact ⟨L,hp,ts,hn,ht,le_trans hU hc⟩

theorem SimpleLowerBound.mono {n T U : Nat} (h : SimpleLowerBound n T) (hU : U ≤ T) :
    SimpleLowerBound n U := by
  rcases h with ⟨L,hp,hs,ts,hn,ht,hc⟩
  exact ⟨L,hp,hs,ts,hn,ht,le_trans hU hc⟩

theorem validate_simple_sound (ls : Array (Line ℤ)) (ts : List Triple) (T : Nat)
    (h : validate ls ts T = true) (hs : NoConcurrent ls.size (linesAt ls)) :
    SimpleLowerBound ls.size T := by
  simp only [validate,Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true] at h
  rcases h with ⟨⟨⟨hp,hn⟩,ht⟩,hc⟩
  refine ⟨fun i => liftLine (linesAt ls i),noParallel_lift _ _ hp,
    noConcurrent_lift _ _ hs,ts,increasing_nodup _ _ hn,?_,hc⟩
  intro t hmem
  exact triangle_lift _ _ _ (ht t hmem)

#print axioms validate_simple_sound

end Kobon
