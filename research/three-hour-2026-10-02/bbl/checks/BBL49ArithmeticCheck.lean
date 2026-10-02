import Kobon.BBLInfinite
namespace Kobon.BBL49VerifiedFamilies
open BBLInfinite
theorem square_identity (t : Nat) : (48*2^t)^2=2304*4^t := by
  have hp : (2^t)^2=4^t := by
    rw [← pow_mul,Nat.mul_comm t 2,pow_mul]
    norm_num
  nlinarith [hp]

theorem count767_formula (t : Nat) : triangleCount 12 767 t=768*4^t-1 := by
  have h := triangleCount_identity 12 767 t
  norm_num only at h
  rw [square_identity] at h
  omega

/-- Arithmetic comparison to the classical odd polynomial benchmark only. -/
theorem odd_polynomial_exact (t : Nat) :
    (48*2^t+1)*(48*2^t-1)/3=768*4^t-1 := by
  have hp : 1≤2^t := Nat.one_le_pow t 2 (by decide)
  have hq : 1≤48*2^t := by omega
  have hs := square_identity t
  have hmul : (48*2^t+1)*(48*2^t-1)+1=(48*2^t)^2 := by
    nlinarith [Nat.sub_add_cancel hq]
  omega

/-- Arithmetic equality with the sharper even simple-arrangement benchmark. -/
theorem even_polynomial_exact (t : Nat) :
    (48*2^t+2)*(2*(48*2^t+2)-5)/6=768*4^t-1+24*2^t := by
  have hp : 1≤2^t := Nat.one_le_pow t 2 (by decide)
  have hp4 : 1≤4^t := Nat.one_le_pow t 4 (by decide)
  have hq : 1≤96*2^t := by omega
  have hc : 1≤768*4^t := by omega
  have hs := square_identity t
  have hsub : 2*(48*2^t+2)-5=96*2^t-1 := by omega
  rw [hsub]
  have hmul : (48*2^t+2)*(96*2^t-1)+2=4608*4^t+144*2^t := by
    nlinarith [Nat.sub_add_cancel hq]
  omega


#print axioms even_polynomial_exact
end Kobon.BBL49VerifiedFamilies
