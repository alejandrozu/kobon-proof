import Kobon.UpperOpenMathTripleGeometry
import Kobon.UpperCoreBudget
import Kobon.UpperTriangleIncidence
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Edge resources forced by matched extremal triple fans

The local geometric incompatibility and actual distinctness of triple-fan
points imply independence of extremal cores. Counting incidences then gives
`3*e <= D2`, without any planarity assumption.

The finite family below has explicit endpoint matching and edge-incidence
equivalences. Those interfaces are not asserted to arise automatically from
an arbitrary arrangement. The aggregate corollaries retain that distinction.
-/
namespace Kobon.UpperOpenMathTripleGraph
open Cells FanGeometry UpperFan UpperTriangleIncidence Finset
open scoped BigOperators

theorem independent_incidence_bound {α : Type*} [DecidableEq α]
    (E : Finset (Finset α)) (X : Finset α)
    (independent : ∀ e∈E, ∀ a∈e∩X, ∀ b∈e∩X, a=b) :
    (∑ a∈X, (E.filter (fun e => a∈e)).card)≤E.card := by
  have he (e : Finset α) (hm : e∈E) : (e∩X).card≤1 :=
    card_le_one.mpr (independent e hm)
  have hid : (∑ a∈X, (E.filter (fun e => a∈e)).card)=
      ∑ e∈E, (e∩X).card := by
    simp only [card_eq_sum_ones,sum_filter]
    rw [sum_comm]
    apply sum_congr rfl
    intro e _
    simp only [← sum_filter]
    congr 1
    ext a
    simp [and_comm]
  rw [hid]
  calc
    _≤∑ _e∈E, 1 := sum_le_sum he
    _=E.card := by simp

structure MatchedTripleFamily (α : Type*) (n : ℕ) (L : ℕ → Line ℝ) where
  fan : α → UpperFan.Sectors n 3 L
  positive : ∀ v z, 0<areaDet (fan v).center ((fan v).point z) ((fan v).point (z+1))
  center_injective : Function.Injective (fun v => (fan v).center)
  edges : Finset Edge
  edge_incidence : ∀ v e, e∈edges ∧ (fan v).center∈e ↔
    ∃ z∈(fan v).coreShared, e={(fan v).center,(fan v).point z}
  matching : ∀ v z, z∈(fan v).coreShared →
    ∃ u : α, ∃ b : ZMod 6,
      (fan u).center=(fan v).point z ∧ (fan u).point b=(fan v).center ∧
      b∈(fan u).coreShared ∧
      (fan u).point (b-1)=(fan v).point (z+1) ∧
      (fan u).point (b+1)=(fan v).point (z-1)

namespace MatchedTripleFamily
variable {α : Type*} [Fintype α] {n : ℕ} {L : ℕ → Line ℝ}
  (F : MatchedTripleFamily α n L)

noncomputable def exceptional : Finset α := by
  classical
  exact univ.filter (fun v => 3≤(F.fan v).ordinaryShared.card)

noncomputable def centers : Finset Point := by
  classical
  exact F.exceptional.image (fun v => (F.fan v).center)

theorem neighbor_not_exceptional (hL : NoParallel n L)
    {v : α} (hv : v∈F.exceptional) (z : ZMod 6) (hz : z∈(F.fan v).coreShared)
    {u : α} (hu : (F.fan u).center=(F.fan v).point z)
    (b : ZMod 6) (hb : (F.fan u).point b=(F.fan v).center)
    (hbc : b∈(F.fan u).coreShared)
    (hm₁ : (F.fan u).point (b-1)=(F.fan v).point (z+1))
    (hm₂ : (F.fan u).point (b+1)=(F.fan v).point (z-1)) : u∉F.exceptional := by
  intro hux
  exact UpperOpenMathRotation.extremal_triple_fans_not_adjacent_at hL
    (F.fan v) (F.fan u) z b (mem_filter.mp hv).2 (mem_filter.mp hux).2
    (mem_sdiff.mp hz).2 (mem_sdiff.mp hbc).2 hu hb hm₁ hm₂ (F.positive v)

theorem edge_centers_independent (hL : NoParallel n L) (e : Edge) (he : e∈F.edges)
    (p : Point) (hp : p∈e∩F.centers) (q : Point) (hq : q∈e∩F.centers) : p=q := by
  classical
  obtain ⟨hpe,hpc⟩ := mem_inter.mp hp
  obtain ⟨hqe,hqc⟩ := mem_inter.mp hq
  obtain ⟨v,hv,rfl⟩ := mem_image.mp hpc
  obtain ⟨w,hw,rfl⟩ := mem_image.mp hqc
  obtain ⟨z,hz,hep⟩ := (F.edge_incidence v e).mp ⟨he,hpe⟩
  have hwp : (F.fan w).center=(F.fan v).center ∨
      (F.fan w).center=(F.fan v).point z := by
    simpa only [hep,mem_insert,mem_singleton] using hqe
  rcases hwp with hsame|hneigh
  · exact hsame.symm
  · obtain ⟨u,b,hu,hb,hbc,hm₁,hm₂⟩ := F.matching v z hz
    have huw : u=w := F.center_injective (hu.trans hneigh.symm)
    subst u
    exact False.elim (F.neighbor_not_exceptional hL hv z hz hu b hb hbc hm₁ hm₂ hw)

omit [Fintype α] in
theorem edge_degree (v : α) :
    (F.edges.filter (fun e => (F.fan v).center∈e)).card=(F.fan v).coreShared.card := by
  classical
  let f := fun z : ZMod 6 => ({(F.fan v).center,(F.fan v).point z} : Edge)
  have he : (F.fan v).coreShared.image f=F.edges.filter (fun e => (F.fan v).center∈e) := by
    ext e
    simp only [mem_image,mem_filter]
    simpa only [f,eq_comm] using (F.edge_incidence v e).symm
  have hinj : Function.Injective f := by
    intro a b h
    have hm : (F.fan v).point a∈f b := by rw [← h]; simp [f]
    have hp : (F.fan v).point a≠(F.fan v).center :=
      UpperOpenMathTripleGeometry.point_ne_center (F.fan v) (F.positive v) a
    have hpq : (F.fan v).point a=(F.fan v).point b := by
      simpa only [f,mem_insert,mem_singleton,or_iff_right hp] using hm
    exact UpperOpenMathTripleGeometry.point_injective (F.fan v) (F.positive v) hpq
  rw [← he,card_image_of_injective _ hinj]

/-- Every exceptional center has three distinct incident graph edges and
no graph edge meets two exceptional centers. Thus those incidences consume
three separate edges per exceptional point. No planar graph theorem is used. -/
theorem three_exceptional_le_edges (hL : NoParallel n L) :
    3*F.exceptional.card≤F.edges.card := by
  classical
  have h := independent_incidence_bound F.edges F.centers (F.edge_centers_independent hL)
  have hs : (∑ p∈F.centers, (F.edges.filter (fun e => p∈e)).card)=3*F.exceptional.card := by
    rw [centers,sum_image]
    · calc
        _=∑ _v∈F.exceptional, 3 := by
          apply sum_congr rfl
          intro v hv
          rw [F.edge_degree]
          exact (F.fan v).core_shared_card_eq_three_of_extremal (by decide) (mem_filter.mp hv).2
        _=3*F.exceptional.card := by simp [Nat.mul_comm]
    · intro a _ b _ h
      exact F.center_injective h
  rw [hs] at h
  exact h

end MatchedTripleFamily

/-- Arithmetic consequence of the now proved independent degree-three
resource count, retaining all remaining geometric aggregate premises. -/
theorem weighted_defect_nonnegative_exception
    (n S I U D₁ D₂ h q e δ : ℤ)
    (incidence : δ=S+U-D₁-D₂) (charging : n-h≤2*U+D₁)
    (core : h≤I-D₂) (fan : 3*D₁+2*D₂≤6*I-8*q+2*e)
    (independent_degree : 3*e≤D₂) :
    n+2*S-7*I+8*q+e≤2*δ ∧
      3*n+6*S-21*I+24*q+D₂≤6*δ := by
  have hw := UpperCoreBudget.weighted_defect_with_core_edges n S I U D₁ D₂ h q e δ
    incidence charging core fan
  constructor <;> omega

#print axioms independent_incidence_bound
#print axioms MatchedTripleFamily.three_exceptional_le_edges
#print axioms weighted_defect_nonnegative_exception
end Kobon.UpperOpenMathTripleGraph
