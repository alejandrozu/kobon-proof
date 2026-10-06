import Kobon.UpperOpenMathOneCapThreeCore
import Kobon.UpperOpenMathUnmarkedCrossResources

/-! The actual one-cap three-core exclusion bounds recipient incidences. -/
namespace Kobon.UpperOpenMathOneCapThreeCoreDegree
open Cells FanGeometry UpperVertexBudget UpperTriangleIncidence UpperSharedIncidence
  UpperCoreExtraction UpperOpenMathCapHeavyTriples UpperOpenMathAntipodalAdjacency
  UpperOpenMathOneCapThreeCore UpperOpenMathUnmarkedCrossResources Finset
set_option maxHeartbeats 1000000

theorem certificate_n13_anti_degree_le_two {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (triples : ∀ c∈core n L, (supports n L c).card=3)
    (p : Point) (hp : p∈core n L)
    (ac : ordinaryDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) p=1)
    (dc : coreDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) p=3) :
    degreeFrom n L (fun a => ofPredicate n L (tri a) hL (ht a))
      (unmarkedFullTwoCapSet n L hL hn tri ht) p≤2 := by
  classical
  let G := fun a => ofPredicate n L (tri a) hL (ht a)
  change ordinaryDegree n L G p=1 at ac
  change coreDegree n L G p=3 at dc
  let A := unmarkedFullTwoCapSet n L hL hn tri ht
  let E := (twoCoreEdges n L G).filter fun e=>p∈e
  let X := E.filter fun e=>(e∩A).Nonempty
  obtain ⟨q,hq,edge,notA⟩ := certificate_n13_has_nonanti_neighbor n L hL hn tri hi ht triples p hp ac dc
  have pnot : p∉A := by
    intro h
    have h2 := (mem_filter.mp h).2.1
    change ordinaryDegree n L G p=2 at h2
    omega
  have inE : ({p,q} : Edge)∈E := mem_filter.mpr ⟨edge,by simp⟩
  have outX : ({p,q} : Edge)∉X := by
    intro h
    obtain ⟨a,ha⟩ := (mem_filter.mp h).2
    obtain ⟨hap,haA⟩ := mem_inter.mp ha
    rcases mem_insert.mp hap with he|he
    · exact pnot (by simpa only [he] using haA)
    · exact notA (by simpa only [mem_singleton.mp he] using haA)
  have proper : X⊂E := Finset.ssubset_iff_subset_ne.mpr ⟨filter_subset _ _,by
    intro he
    rw [he] at outX
    exact outX inE⟩
  have lt := card_lt_card proper
  have ec : E.card=3 := dc
  have eq : degreeFrom n L G A p=X.card := by
    apply congrArg Finset.card
    ext e
    simp only [degreeFrom,X,E,mem_filter,and_assoc]
  rw [ec] at lt
  rw [eq]
  omega

#print axioms certificate_n13_anti_degree_le_two
end Kobon.UpperOpenMathOneCapThreeCoreDegree
