import Kobon.StrictLinearCertificate
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-! The two automatic coefficient identities reduce an intercept-grid
Farkas certificate by two columns. This explains the exact local interval
audit, but does not assert that the external interval computation was itself
checked in Lean. -/
namespace Kobon.BBLObstructionReduction
open scoped BigOperators

theorem sum_two_support {d : Nat} (f : Fin d→ℝ) (p q : Fin d) (hpq : p≠q)
    (hz : ∀ j, j≠p→j≠q→f j=0) : (∑ j, f j)=f p+f q := by
  have he (j : Fin d) : f j=(if j=p then f p else 0)+(if j=q then f q else 0) := by
    by_cases hjp : j=p
    · subst j; simp [hpq]
    by_cases hjq : j=q
    · subst j; simp [Ne.symm hpq]
    simp [hjp,hjq,hz j hjp hjq]
  calc
    (∑ j, f j)=(∑ j, ((if j=p then f p else 0)+(if j=q then f q else 0))) :=
      Finset.sum_congr rfl (fun j _ => he j)
    _=f p+f q := by rw [Finset.sum_add_distrib]; simp

/-- If every row annihilates the constant vector and the intercept vector,
the final two coefficient equations follow from all the others, provided
the two omitted intercepts are distinct. -/
theorem two_columns_follow {m d : Nat} (A : Fin m→Fin d→ℝ)
    (a : Fin d→ℝ) (w : Fin m→ℝ) (p q : Fin d) (hpq : p≠q) (ha : a p≠a q)
    (hconst : ∀ i, (∑ j, A i j)=0)
    (hlinear : ∀ i, (∑ j, A i j*a j)=0)
    (hother : ∀ j, j≠p→j≠q→(∑ i, w i*A i j)=0) :
    ∀ j, (∑ i, w i*A i j)=0 := by
  let C : Fin d→ℝ := fun j => ∑ i, w i*A i j
  have hs : (∑ j, C j)=0 := by
    change (∑ j, ∑ i, w i*A i j)=0
    rw [Finset.sum_comm]
    simp_rw [←Finset.mul_sum,hconst,mul_zero]
    simp
  have ht : (∑ j, C j*a j)=0 := by
    change (∑ j, (∑ i, w i*A i j)*a j)=0
    simp_rw [Finset.sum_mul,mul_assoc]
    rw [Finset.sum_comm]
    simp_rw [←Finset.mul_sum,hlinear,mul_zero]
    simp
  have hs2 : C p+C q=0 := by
    rw [sum_two_support C p q hpq hother] at hs
    exact hs
  have ht2 : C p*a p+C q*a q=0 := by
    rw [sum_two_support (fun j => C j*a j) p q hpq
      (fun j hjp hjq => by simp [C,hother j hjp hjq])] at ht
    exact ht
  have hm : (a p-a q)*C p=0 := by linear_combination ht2-a q*hs2
  have hcp : C p=0 := (mul_eq_zero.mp hm).resolve_left (sub_ne_zero.mpr ha)
  have hcq : C q=0 := by linarith
  intro j
  by_cases hjp : j=p
  · simpa [hjp] using hcp
  by_cases hjq : j=q
  · simpa [hjq] using hcq
  exact hother j hjp hjq

theorem reduced_infeasible {m d : Nat} (A : Fin m→Fin d→ℝ)
    (a : Fin d→ℝ) (w : Fin m→ℝ) (p q : Fin d) (hpq : p≠q) (ha : a p≠a q)
    (hconst : ∀ i, (∑ j, A i j)=0)
    (hlinear : ∀ i, (∑ j, A i j*a j)=0)
    (hother : ∀ j, j≠p→j≠q→(∑ i, w i*A i j)=0)
    (hw : ∀ i, 0≤w i) (hpos : ∃ i, 0<w i) :
    ¬ ∃ v : Fin d→ℝ, ∀ i, 0<∑ j, A i j*v j :=
  StrictLinearCertificate.homogeneous_infeasible A w hw hpos
    (two_columns_follow A a w p q hpq ha hconst hlinear hother)

#print axioms two_columns_follow
#print axioms reduced_infeasible
end Kobon.BBLObstructionReduction
