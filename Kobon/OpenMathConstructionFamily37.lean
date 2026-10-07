import Kobon.OpenMathConstructionSeed37Normalized
import Kobon.BBLInfinite
import Kobon.OpenMathBoundarySuccessor
import Kobon.UpperSimpleOptimality
import Kobon.UpperEvenSimpleOptimality

/-! Geometric completion of the q36 orbit, a tail of the known q18 numerical
family of Parpalak--Utkin/Blanc. The competition point is credited to Rohith
Poola. A new fixed-slope whole-interval certificate supplies the compatible
seed. Every even companion follows from the universal deficit-two successor,
so no separately assumed or finitely sampled visible direction is required.
-/
namespace Kobon.OpenMathConstructionFamily37
open BBLInfinite
set_option autoImplicit false
set_option maxHeartbeats 1000000

def q (t : Nat) : Nat := 36*2^t
def oddCount (t : Nat) : Nat := 432*4^t-1
def evenCount (t : Nat) : Nat := oddCount t+18*2^t

theorem uniform_seed : UniformSeed 9 431 := by
  refine ⟨1/100000000,by norm_num,?_⟩
  intro ε he hu
  exact OpenMathConstructionSeed37Normalized.compatible ε he hu.le

theorem q_positive (t : Nat) : 36≤q t := by
  have h := Nat.one_le_pow t 2 (by decide)
  unfold q
  omega

theorem square_identity (t : Nat) : (q t)^2=1296*4^t := by
  have hp : (2^t)^2=4^t := by
    rw [← pow_mul,Nat.mul_comm t 2,pow_mul]
    norm_num
  unfold q
  nlinarith

theorem count_formula (t : Nat) : triangleCount 9 431 t=oddCount t := by
  have h := triangleCount_identity 9 431 t
  have hs : (4*9*2^t)^2=1296*4^t := square_identity t
  rw [hs] at h
  norm_num at h
  have hp := Nat.one_le_pow t 4 (by decide)
  unfold oddCount
  omega

theorem count_identity (t : Nat) : 3*oddCount t+3=(q t)^2 := by
  have h := triangleCount_identity 9 431 t
  rw [count_formula] at h
  change 3*oddCount t+1296=1293+(q t)^2 at h
  omega

theorem odd_family (t : Nat) : SimpleLowerBound (q t+1) (oddCount t) := by
  have h := infinite_family 9 431 (by decide) uniform_seed t
  simpa only [q,count_formula,show 4*9=36 by decide] using h

theorem even_family (t : Nat) : SimpleLowerBound (q t+2) (evenCount t) := by
  let m := 18*2^t
  have hm : 1≤m := by
    have h := Nat.one_le_pow t 2 (by decide)
    dsimp [m]
    omega
  have hq : q t=2*m := by dsimp [q,m]; ring
  have ho := odd_family t
  rw [hq] at ho
  have hc : 3*(oddCount t : ℤ)+3=(q t : ℤ)^2 := by
    exact_mod_cast count_identity t
  have hqi : (q t : ℤ)=2*(m : ℤ) := by exact_mod_cast hq
  rw [hqi] at hc
  have hd : ((2*m+1 : Nat) : ℤ)*(2*(m : ℤ)-1)-3*(oddCount t : ℤ)≤2 := by
    push_cast
    nlinarith [hc,hqi]
  have h := OpenMathBoundarySuccessor.odd_defect_two_successor m (oddCount t) hm ho hd
  convert h using 1 <;> dsimp [q,m,evenCount] <;> ring

theorem even_classical (t : Nat) : LowerBound (q t+2) (evenCount t) :=
  (even_family t).classical

theorem odd_polynomial_exact (t : Nat) :
    (q t+1)*(q t+1-2)/3=oddCount t := by
  have hp := q_positive t
  have hc := count_identity t
  have hs : q t+1-2+1=q t := by omega
  have he : (q t+1)*(q t+1-2)+1=(q t)^2 := by nlinarith
  omega

theorem even_polynomial_exact (t : Nat) :
    (q t+2)*(2*(q t+2)-5)/6=evenCount t := by
  have hp := q_positive t
  have hc := count_identity t
  have hm : 2*(18*2^t)=q t := by unfold q; ring
  have hs : 2*(q t+2)-5+1=2*q t := by omega
  have he : (q t+2)*(2*(q t+2)-5)+2=2*(q t)^2+3*q t := by nlinarith
  unfold evenCount
  omega

theorem odd_optimal_in_simple_arrangements (t : Nat) :
    SimpleLowerBound (q t+1) (oddCount t) ∧
      ∀ T, SimpleLowerBound (q t+1) T → T≤oddCount t := by
  refine ⟨odd_family t,?_⟩
  intro T h
  have hp := q_positive t
  have hu := UpperSimpleOptimality.simple_lower_bound_floor (q t+1) T (by omega) h
  simpa only [odd_polynomial_exact] using hu

theorem even_optimal_in_simple_arrangements (t : Nat) :
    SimpleLowerBound (q t+2) (evenCount t) ∧
      ∀ T, SimpleLowerBound (q t+2) T → T≤evenCount t := by
  refine ⟨even_family t,?_⟩
  intro T h
  have hp := q_positive t
  have heven : (q t+2)%2=0 := by simp [q,Nat.add_mod,Nat.mul_mod]
  have hu := UpperEvenSimpleOptimality.simple_lower_bound_even_floor (q t+2) T
    (by omega) heven h
  simpa only [even_polynomial_exact] using hu

#print axioms uniform_seed
#print axioms odd_family
#print axioms even_family
#print axioms even_optimal_in_simple_arrangements
end Kobon.OpenMathConstructionFamily37
