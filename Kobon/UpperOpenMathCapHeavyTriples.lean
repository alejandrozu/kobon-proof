import Kobon.UpperOpenMathActualMatching
import Kobon.UpperOpenMathPartialTriple
import Kobon.UpperOpenMathSupportedCores
import Kobon.UpperOpenMathTripleGraph

/-!
# An actual independent set including partial cap-heavy triple fans

Extremal full triple cores and partial triple cores with ordinary degree two
and core degree one cannot be joined by a shared core edge. This strengthens
the formerly conditional extremal-triple independence statement by including
the four-run pattern. It is a generalization/formalization of the related
OpenMath cap/bridge obstruction, not an assertion of sole discovery priority.
-/
namespace Kobon.UpperOpenMathCapHeavyTriples
open Cells FanGeometry UpperVertexBudget UpperTriangleIncidence UpperSharedIncidence
  UpperCoreExtraction UpperOpenMathRadialOrder UpperOpenMathActualFans Finset

noncomputable def ordinaryDegree {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (G : α → TriangleGeometry) (c : Point) : ℕ := by
  classical
  exact ((oneCoreEdges n L G).filter (fun e => c∈e)).card

noncomputable def coreDegree {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (G : α → TriangleGeometry) (c : Point) : ℕ := by
  classical
  exact ((twoCoreEdges n L G).filter (fun e => c∈e)).card

def CapHeavy {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (G : α → TriangleGeometry) (c : Point) : Prop :=
  (supports n L c).card=3 ∧
    (ordinaryDegree n L G c=3 ∨ (ordinaryDegree n L G c=2 ∧ coreDegree n L G c=1))

/-- No shared core edge joins two cap-heavy triple points. All fan matching
and ordinary/core incidence identities are extracted from the actual chosen
certificate family. -/
theorem certificate_cap_heavy_not_adjacent {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (c d : Point) (hc : c∈core n L) (hd : d∈core n L)
    (hcapc : CapHeavy n L (fun a => ofPredicate n L (tri a) hL (ht a)) c)
    (hcapd : CapHeavy n L (fun a => ofPredicate n L (tri a) hL (ht a)) d)
    (edge : {c,d}∈twoCoreEdges n L (fun a => ofPredicate n L (tri a) hL (ht a))) : False := by
  classical
  let G := fun a => ofPredicate n L (tri a) hL (ht a)
  obtain ⟨rc,kc⟩ := hcapc
  obtain ⟨rd,kd⟩ := hcapd
  letI : NeZero (2*(supports n L c).card) := ⟨by omega⟩
  letI : NeZero (2*(supports n L d).card) := ⟨by omega⟩
  let D := atPoint n L hL hn c
  let E := atPoint n L hL hn d
  let f := fan n L hL hn tri ht c (mem_filter.mp hc).1 D (by omega)
  let g := fan n L hL hn tri ht d (mem_filter.mp hd).1 E (by omega)
  have used := (mem_filter.mp (mem_sdiff.mp edge).1).1
  have neq : d≠c := by
    intro he
    have hcard := used_edge_card G used
    simp only [he,insert_eq_of_mem (mem_singleton_self c),card_singleton] at hcard
    omega
  obtain ⟨z,hz⟩ := UpperOpenMathSectorRecords.used_edge_has_ray n L hL hn tri ht c
    (mem_filter.mp hc).1 D d neq used
  change f.point z=d at hz
  have fcore : z∈f.coreShared :=
    (fan_core_iff n L hL hn tri ht c (mem_filter.mp hc).1 D (by omega) hi hc z).mpr
      (by rw [hz]; exact edge)
  obtain ⟨w,gcore,gw,right,left⟩ := UpperOpenMathActualMatching.certificate_neighbor_matching
    n L hL hn tri hi ht c d hc hd D E (by omega) (by omega) z fcore hz.symm
  have fp : z-1∈f.ordinaryShared := by
    rcases kc with kc|⟨ko,kk⟩
    · apply UpperOpenMathPartialTriple.ordinary_previous_of_extremal_card rc f _ z fcore
      rw [fan_ordinary_card n L hL hn tri ht c (mem_filter.mp hc).1 D (by omega) hi hc]
      exact Nat.le_of_eq kc.symm
    · apply UpperOpenMathPartialTriple.ordinary_previous_of_two_one_card rc f _ _ z fcore
      · rw [fan_ordinary_card n L hL hn tri ht c (mem_filter.mp hc).1 D (by omega) hi hc]
        exact ko
      · rw [fan_core_card n L hL hn tri ht c (mem_filter.mp hc).1 D (by omega) hi hc]
        exact kk
  have gp : w-1∈g.ordinaryShared := by
    rcases kd with kd|⟨ko,kk⟩
    · apply UpperOpenMathPartialTriple.ordinary_previous_of_extremal_card rd g _ w gcore
      rw [fan_ordinary_card n L hL hn tri ht d (mem_filter.mp hd).1 E (by omega) hi hd]
      exact Nat.le_of_eq kd.symm
    · apply UpperOpenMathPartialTriple.ordinary_previous_of_two_one_card rd g _ _ w gcore
      · rw [fan_ordinary_card n L hL hn tri ht d (mem_filter.mp hd).1 E (by omega) hi hd]
        exact ko
      · rw [fan_core_card n L hL hn tri ht d (mem_filter.mp hd).1 E (by omega) hi hd]
        exact kk
  exact UpperOpenMathPartialTriple.incompatible_partial_triple_fans_card rc rd hL f g z w
    fp gp hz.symm gw right left (fan_positive n L hL hn tri ht c (mem_filter.mp hc).1 D (by omega))

noncomputable def capHeavySet {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (G : α → TriangleGeometry) : Finset Point := by
  classical
  exact (core n L).filter (CapHeavy n L G)

/-- The actual degrees of the cap-heavy triple points consume separate
core-to-core edges. Full extremal triples contribute three incidences and
four-run two-cap triples contribute one. -/
theorem certificate_cap_heavy_degree_sum {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a)) :
    let G := fun a => ofPredicate n L (tri a) hL (ht a)
    (∑ c∈capHeavySet n L G, coreDegree n L G c)≤(twoCoreEdges n L G).card := by
  classical
  let G := fun a => ofPredicate n L (tri a) hL (ht a)
  let X := capHeavySet n L G
  have independent (e : Edge) (he : e∈twoCoreEdges n L G)
      (p : Point) (hp : p∈e∩X) (q : Point) (hq : q∈e∩X) : p=q := by
    by_contra hneq
    have hpE := (mem_inter.mp hp).1
    have hqE := (mem_inter.mp hq).1
    have hpX := mem_filter.mp (mem_inter.mp hp).2
    have hqX := mem_filter.mp (mem_inter.mp hq).2
    have heused := (mem_filter.mp (mem_sdiff.mp he).1).1
    have hpair : e={p,q} := by
      apply Eq.symm
      apply eq_of_subset_of_card_le
      · intro a ha
        simp only [mem_insert,mem_singleton] at ha
        rcases ha with rfl|rfl <;> assumption
      · rw [card_pair hneq,used_edge_card G heused]
    exact certificate_cap_heavy_not_adjacent n L hL hn tri hi ht p q hpX.1 hqX.1 hpX.2 hqX.2
      (by simpa only [hpair] using he)
  exact UpperOpenMathTripleGraph.independent_incidence_bound (twoCoreEdges n L G) X independent

#print axioms certificate_cap_heavy_not_adjacent
#print axioms certificate_cap_heavy_degree_sum
end Kobon.UpperOpenMathCapHeavyTriples
