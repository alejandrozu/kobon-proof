import Kobon.UpperFanSupport
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# A boundary bridge for finite collections of multiple-point fans

An actual supporting line for the finite set of core points rules out an
extremal fan at that point. The endpoint-to-core map is explicit. These are
real-geometric theorems, but extracting all the local fan data and the global
edge budget from an arbitrary arrangement remains a separate task.
-/

namespace Kobon.UpperCoreBoundary
open Cells FanGeometry UpperFan UpperFanSupport Finset
open scoped BigOperators

/-- Any core point with a supporting line has the sharpened ordinary-ray
bound, independently of its number of core-ended shared rays. -/
theorem bound_at_supported_core {n r : ℕ} [NeZero (2*r)]
    {L : ℕ → Line ℝ} (f : UpperFan.Sectors n r L) (hr : 3≤r)
    (positive : ∀ z, 0<areaDet f.center (f.point z) (f.point (z+1)))
    (P : Finset Point)
    (endpoint_map : ∀ z∈f.coreShared, f.point z∈P)
    (w : Line ℝ) (hw : affineEval w f.center=0)
    (valid : w.a≠0 ∨ w.b≠0)
    (support : ∀ p∈P, 0≤affineEval w p) :
    f.ordinaryShared.card≤2*r-4 := by
  by_contra hh
  have hcard : 2*r-3≤f.ordinaryShared.card := by omega
  obtain ⟨z,hz,hn⟩ := UpperFanSupport.Sectors.extremal_core_not_in_halfplane
    f hr hcard positive w hw valid
  have hp := support (f.point z) (endpoint_map z hz)
  linarith

/-- A finite collection of actual fans. No conclusion that every arrangement
already produces this structure is built into its definition. -/
structure CoreFamily (α : Type*) (n : ℕ) (L : ℕ → Line ℝ) where
  multiplicity : α → ℕ
  at_least_three : ∀ v, 3≤multiplicity v
  nonzero : ∀ v, NeZero (2*multiplicity v)
  fan : (v : α) → @UpperFan.Sectors n (multiplicity v) (nonzero v) L
  positive : ∀ v z, 0<areaDet (fan v).center ((fan v).point z)
    ((fan v).point (z+1))
  core_endpoint : ∀ v z, z∈(fan v).coreShared →
    ∃ u : α, (fan v).point z=(fan u).center

namespace CoreFamily
variable {α : Type*} [Fintype α] {n : ℕ} {L : ℕ → Line ℝ}
  (F : CoreFamily α n L)

local instance (v : α) : NeZero (2*F.multiplicity v) := F.nonzero v

/-- The supporting-line condition is a concrete geometric premise. -/
def Supported (v : α) : Prop := ∃ w : Line ℝ,
  affineEval w (F.fan v).center=0 ∧ (w.a≠0 ∨ w.b≠0) ∧
  ∀ u : α, 0≤affineEval w (F.fan u).center

theorem bound_at_supported (v : α) (hv : F.Supported v) :
    (F.fan v).ordinaryShared.card≤2*F.multiplicity v-4 := by
  classical
  letI : NeZero (2*F.multiplicity v) := F.nonzero v
  obtain ⟨w,hw,valid,hs⟩ := hv
  let P : Finset Point := univ.image (fun u : α => (F.fan u).center)
  apply bound_at_supported_core (F.fan v) (F.at_least_three v) (F.positive v)
    P ?_ w hw valid ?_
  · intro z hz
    obtain ⟨u,hu⟩ := F.core_endpoint v z hz
    exact mem_image.mpr ⟨u,mem_univ u,hu.symm⟩
  · intro p hp
    obtain ⟨u,_,rfl⟩ := mem_image.mp hp
    exact hs u

/-- Summed gain for any explicitly supplied set of supported core points.
This is a fan-incidence theorem; it is not yet the global triangle budget. -/
theorem sum_ordinary_bound (B : Finset α)
    (supported : ∀ v∈B, F.Supported v) :
    (∑ v, ((F.fan v).ordinaryShared.card : ℤ))≤
      2*(∑ v, (F.multiplicity v : ℤ))-3*Fintype.card α-B.card := by
  classical
  have local_bound (v : α) : ((F.fan v).ordinaryShared.card : ℤ)≤
      2*(F.multiplicity v : ℤ)-3-(if v∈B then 1 else 0) := by
    letI : NeZero (2*F.multiplicity v) := F.nonzero v
    have hr := F.at_least_three v
    by_cases hv : v∈B
    · have hb := F.bound_at_supported v (supported v hv)
      simp only [hv,ite_true]
      omega
    · have hb := (F.fan v).ordinary_shared_card_le hr
      simp only [hv,ite_false]
      omega
  have hh := sum_le_sum (s:=univ) (fun v _ => local_bound v)
  simpa only [sum_sub_distrib,← mul_sum,sum_const,nsmul_eq_mul,card_univ,
    sum_boole,filter_mem_eq_inter,univ_inter,mul_comm] using hh

end CoreFamily

#print axioms bound_at_supported_core
#print axioms CoreFamily.bound_at_supported
#print axioms CoreFamily.sum_ordinary_bound
end Kobon.UpperCoreBoundary

