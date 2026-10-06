import Kobon.UpperOpenMathFullCoreSides
import Kobon.UpperOpenMathAntipodalAdjacency

/-! A one-cap, three-core triple cannot have three antipodal full neighbors.
The obstruction is the selected cap side between an adjacent pair of core rays.
-/
namespace Kobon.UpperOpenMathOneCapThreeCore
open Cells FanGeometry UpperFan UpperVertexBudget UpperTriangleIncidence
  UpperSharedIncidence UpperCoreExtraction UpperOpenMathRadialOrder
  UpperOpenMathSectorRecords UpperOpenMathActualFans UpperOpenMathCapHeavyTriples
  UpperOpenMathAntipodalAdjacency Finset
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem finite_three_core_adjacent : ∀ T C : Finset (ZMod 6),
    C⊆T.filter (fun z=>z-1∈T) → C.card=3 →
    (T.filter (fun z=>z-1∈T)).card=4 → ∃ z∈C, z+1∈C := by
  decide +kernel

theorem three_core_adjacent {n r : ℕ} [NeZero (2*r)] {L : ℕ → Line ℝ}
    (f : Sectors n r L) (hr : r=3)
    (ac : f.ordinaryShared.card=1) (dc : f.coreShared.card=3) :
    ∃ z∈f.coreShared, z+1∈f.coreShared := by
  subst r
  have sc : f.shared.card=4 := by have h := f.shared_card_split; omega
  exact finite_three_core_adjacent f.triangular f.coreShared
    (sdiff_subset) dc sc

theorem certificate_n13_has_nonanti_neighbor {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (triples : ∀ c∈core n L, (supports n L c).card=3)
    (c : Point) (hc : c∈core n L)
    (ac : ordinaryDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) c=1)
    (dc : coreDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) c=3) :
    ∃ q∈core n L, {c,q}∈twoCoreEdges n L (fun a => ofPredicate n L (tri a) hL (ht a)) ∧
      q∉unmarkedFullTwoCapSet n L hL hn tri ht := by
  classical
  let G := fun a => ofPredicate n L (tri a) hL (ht a)
  let A := unmarkedFullTwoCapSet n L hL hn tri ht
  have rc := triples c hc
  letI : NeZero (2*(supports n L c).card) := ⟨by omega⟩
  let D := atPoint n L hL hn c
  let f := fan n L hL hn tri ht c (mem_filter.mp hc).1 D (by omega)
  have ord : f.ordinaryShared.card=1 :=
    (fan_ordinary_card n L hL hn tri ht c (mem_filter.mp hc).1 D (by omega) hi hc).trans ac
  have cor : f.coreShared.card=3 :=
    (fan_core_card n L hL hn tri ht c (mem_filter.mp hc).1 D (by omega) hi hc).trans dc
  obtain ⟨z,hz,hnz⟩ := three_core_adjacent f rc ord cor
  have qC := fan_core_endpoint n L hL hn tri ht c (mem_filter.mp hc).1 D (by omega) hi hc z hz
  have rC := fan_core_endpoint n L hL hn tri ht c (mem_filter.mp hc).1 D (by omega) hi hc (z+1) hnz
  have qE := (fan_core_iff n L hL hn tri ht c (mem_filter.mp hc).1 D (by omega) hi hc z).mp hz
  have rE := (fan_core_iff n L hL hn tri ht c (mem_filter.mp hc).1 D (by omega) hi hc (z+1)).mp hnz
  by_cases qa : f.point z∈A
  · by_cases ra : f.point (z+1)∈A
    · have zT : z∈f.triangular := (mem_filter.mp (mem_sdiff.mp hz).1).1
      obtain ⟨o⟩ := (mem_triangular G c f.point z).mp zT
      have cap := transported_side_used G o.index o.triangle o.transport 1
      change ({o.triangle.q,o.triangle.r} : Edge)∈usedEdges G at cap
      rw [o.left,o.right] at cap
      obtain ⟨qCore,qa2,qd4,qm0⟩ := mem_filter.mp qa
      obtain ⟨rCore,ra2,rd4,rm0⟩ := mem_filter.mp ra
      change ordinaryDegree n L G (f.point z)=2 at qa2
      change coreDegree n L G (f.point z)=4 at qd4
      have rq := triples (f.point z) qCore
      have qfull : ordinaryDegree n L G (f.point z)+coreDegree n L G (f.point z)=
          2*(supports n L (f.point z)).card := by omega
      have shared := UpperOpenMathFullCoreSides.certificate_full_core_side_shared
        n L hL hn tri hi ht (f.point z) (f.point (z+1)) qCore rCore cap qfull
      exact False.elim (certificate_unmarked_full_not_adjacent n L hL hn tri hi ht triples
        (f.point z) (f.point (z+1)) qCore rCore qa2 ra2 qd4 rd4 qm0 rm0 shared)
    · exact ⟨f.point (z+1),rC,rE,ra⟩
  · exact ⟨f.point z,qC,qE,qa⟩

#print axioms finite_three_core_adjacent
#print axioms certificate_n13_has_nonanti_neighbor
end Kobon.UpperOpenMathOneCapThreeCore
