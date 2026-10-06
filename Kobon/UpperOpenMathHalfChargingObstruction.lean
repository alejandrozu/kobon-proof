import Kobon.UpperOpenMathHalfCurvatureWeights

/-! Sharpness of the finite charging relaxation, not a realizable line
arrangement or a counterexample to a stronger geometric theorem. The graph
has two unmarked full sources, two N13 recipients, two marked full sources,
and one poor recipient. Extra geometric restrictions are needed to improve
the half coefficient beyond these numerical and incidence constraints. -/
namespace Kobon.UpperOpenMathHalfChargingObstruction
open Finset
open scoped BigOperators

def a : Fin 7 → ℕ := ![2,2,1,1,2,2,0]
def d : Fin 7 → ℕ := ![4,4,3,3,4,4,2]
def m : Fin 7 → ℕ := ![0,0,0,0,1,1,0]
def x : Fin 7 → ℕ := ![0,0,2,2,0,0,0]
def P : Finset (Fin 7) := univ
def A : Finset (Fin 7) := P.filter (fun p => a p=2 ∧ d p=4 ∧ m p=0)
def B : Finset (Fin 7) := P.filter (fun p => a p≤1 ∧ a p+d p≤2)
def F : Finset (Fin 7) := P.filter (fun p => a p=1 ∧ d p=5)
def W : ℤ := ∑ p∈P, (6-2*(a p : ℤ)-d p)
def E : Finset (Finset (Fin 7)) :=
  {{0,2},{0,3},{0,4},{0,5},{1,2},{1,3},{1,4},{1,5},
   {2,3},{4,5},{4,6},{5,6}}

theorem numerical_hypotheses :
    (∀ p∈P, a p≤3 ∧ a p+d p≤6 ∧ a p+d p≠5) ∧
    (∀ p∈P, a p=3 → d p=3 ∧ m p=3) ∧
    (∀ p∈P, x p≤d p) ∧
    (∀ p∈P, a p+d p=6 → x p=0) ∧
    (∀ p∈P, a p=2 → d p=2 → m p=0 → x p=0) ∧
    (∀ p∈P, a p=1 → d p=3 → x p≤2) ∧
    ((∑ p∈P,m p)+(∑ p∈B,x p)≤∑ p∈B,d p) ∧
    (2*A.card≤∑ p∈P,x p) := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> decide +kernel

theorem graph_incidence_hypotheses :
    (∀ e∈E, e.card=2) ∧
    (∀ p∈P, (E.filter (fun e => p∈e)).card=d p) ∧
    (∀ p∈P, (if a p+d p=6 then 0 else
      (E.filter (fun e => p∈e ∧ (e∩A).Nonempty)).card)=x p) ∧
    (∀ e∈E, (e∩A).card≤1) := by decide +kernel

theorem equality_and_stronger_coefficient_failure :
    W=-2 ∧ A.card=2 ∧ F.card=0 ∧
    2*W+2*(A.card : ℤ)+2*(F.card : ℤ)=0 ∧
    ¬0≤2*W+(A.card : ℤ)+2*(F.card : ℤ) := by decide +kernel

#print axioms numerical_hypotheses
#print axioms graph_incidence_hypotheses
#print axioms equality_and_stronger_coefficient_failure
end Kobon.UpperOpenMathHalfChargingObstruction
