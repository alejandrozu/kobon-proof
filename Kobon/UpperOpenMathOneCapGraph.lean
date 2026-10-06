import Kobon.UpperOpenMathCoreGraphCounts

/-! Finite graph arithmetic for the single full one-cap equality case.
The actual fan incompatibility supplying the no-R--R hypothesis is proved
separately; no geometric assumption is hidden in this graph lemma. -/
namespace Kobon.UpperOpenMathOneCapGraph
open Finset

theorem neighbor_degree_tradeoff {β : Type*} [Fintype β] [DecidableEq β]
    (H : SimpleGraph β) [DecidableRel H.Adj] (b u : β) (R : β → Prop)
    (types : ∀ v, v=b ∨ v=u ∨ R v)
    (degreeR : ∀ v, R v → 2≤H.degree v)
    (noRR : ∀ r q, H.Adj b r → R r → R q → ¬H.Adj r q) :
    H.degree b≤H.degree u+1 := by
  classical
  have second (r : β) (br : H.Adj b r) (hr : R r) : H.Adj r u := by
    by_contra no
    have subset : H.neighborFinset r⊆{b} := by
      intro q hq
      have rq := (SimpleGraph.mem_neighborFinset H r q).mp hq
      rcases types q with eq|eq|hqR
      · simpa only [mem_singleton] using eq
      · exact False.elim (no (by simpa only [eq] using rq))
      · exact False.elim (noRR r q br hr hqR rq)
    have card := card_le_card subset
    rw [SimpleGraph.card_neighborFinset_eq_degree,card_singleton] at card
    have lower := degreeR r hr
    omega
  have subset : (H.neighborFinset b).erase u⊆H.neighborFinset u := by
    intro r hr
    obtain ⟨ru,rb⟩ := mem_erase.mp hr
    have br := (SimpleGraph.mem_neighborFinset H b r).mp rb
    have rR : R r := by
      rcases types r with eq|eq|h
      · exact False.elim (br.ne' eq)
      · exact False.elim (ru eq)
      · exact h
    exact (SimpleGraph.mem_neighborFinset H u r).mpr (second r br rR).symm
  have bound := card_le_card subset
  rw [SimpleGraph.card_neighborFinset_eq_degree] at bound
  by_cases hu : u∈H.neighborFinset b
  · rw [card_erase_of_mem hu,SimpleGraph.card_neighborFinset_eq_degree] at bound
    omega
  · rw [erase_eq_of_notMem hu,SimpleGraph.card_neighborFinset_eq_degree] at bound
    omega

theorem five_three_impossible {β : Type*} [Fintype β] [DecidableEq β]
    (H : SimpleGraph β) [DecidableRel H.Adj] (b u : β) (R : β → Prop)
    (types : ∀ v, v=b ∨ v=u ∨ R v)
    (degreeB : 5≤H.degree b) (degreeU : H.degree u≤3)
    (degreeR : ∀ v, R v → 2≤H.degree v)
    (noRR : ∀ r q, H.Adj b r → R r → R q → ¬H.Adj r q) : False := by
  have h := neighbor_degree_tradeoff H b u R types degreeR noRR
  omega

#print axioms neighbor_degree_tradeoff
#print axioms five_three_impossible
end Kobon.UpperOpenMathOneCapGraph
