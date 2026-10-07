import Kobon.UpperOpenMathUnmarkedPoorResources
import Kobon.UpperOpenMathNormalizedActualFull

/-! A balanced pair cannot use a full third core as a neighboring apex. -/
namespace Kobon.UpperOpenMathBalancedFullBridge
open Cells FanGeometry UpperVertexBudget UpperTriangleIncidence UpperSharedIncidence
  UpperCoreExtraction UpperOpenMathCapHeavyTriples UpperOpenMathCoreComponents
  UpperOpenMathMarkedPorts UpperOpenMathUnmarkedPoorResources Finset

theorem degree_two_neighbor_cases {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (G : α → TriangleGeometry)
    (p q c : Point) (degree : coreDegree n L G p=2)
    (pq : {p,q}∈twoCoreEdges n L G) (pc : {p,c}∈twoCoreEdges n L G)
    (qc : q≠c)
    (d : Point) (pd : {p,d}∈twoCoreEdges n L G) : d=q ∨ d=c := by
  classical
  let E := (twoCoreEdges n L G).filter (fun e => p∈e)
  have eq : E={{p,q},{p,c}} := by
    apply Eq.symm
    apply eq_of_subset_of_card_le
    · intro e he
      rcases mem_insert.mp he with he|he
      · exact mem_filter.mpr ⟨he ▸ pq,by simp [he]⟩
      · exact mem_filter.mpr ⟨mem_singleton.mp he ▸ pc,by simp [mem_singleton.mp he]⟩
    · have ne : ({p,q} : Edge)≠{p,c} := fun h => qc (pair_insert_injective p h)
      change coreDegree n L G p≤({({p,q} : Edge),{p,c}} : Finset Edge).card
      rw [degree,card_pair ne]
  have mem : ({p,d} : Edge)∈E := mem_filter.mpr ⟨pd,by simp⟩
  rw [eq] at mem
  rcases mem_insert.mp mem with first|second
  · exact Or.inl (pair_insert_injective p first)
  · exact Or.inr (pair_insert_injective p (mem_singleton.mp second))

theorem certificate_balanced_pair_next_to_full_impossible {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (p q c : Point) (hp : p∈core n L) (hq : q∈core n L) (hc : c∈core n L)
    (rp : (supports n L p).card=3) (rq : (supports n L q).card=3) (rc : (supports n L c).card=3)
    (ap : ordinaryDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) p=2)
    (dp : coreDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) p=2)
    (mp : markedCount n L hL hn tri ht p=0)
    (aq : ordinaryDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) q=2)
    (dq : coreDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) q=2)
    (mq : markedCount n L hL hn tri ht q=0)
    (full : ordinaryDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) c+
      coreDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) c=6)
    (pq : {p,q}∈twoCoreEdges n L (fun a => ofPredicate n L (tri a) hL (ht a)))
    (pc : {p,c}∈twoCoreEdges n L (fun a => ofPredicate n L (tri a) hL (ht a))) : False := by
  classical
  let G := fun a => ofPredicate n L (tri a) hL (ht a)
  have qc : q≠c := by
    intro he
    have aq' : ordinaryDegree n L G q=2 := aq
    have dq' : coreDegree n L G q=2 := dq
    have full' : ordinaryDegree n L G c+coreDegree n L G c=6 := full
    rw [he] at aq' dq'
    omega
  obtain ⟨f,fc,df⟩ := certificate_normalized_two_two_of_zero_marks n L hL hn tri hi ht p hp rp ap dp mp
  have neighbors (d : Point) (hd : d∈core n L) (edge : {f.center,d}∈twoCoreEdges n L G) :
      (supports n L d).card=3 ∧ ((ordinaryDegree n L G d=2 ∧ coreDegree n L G d=2 ∧
        markedCount n L hL hn tri ht d=0) ∨ ordinaryDegree n L G d+coreDegree n L G d=6) := by
    have edge' : {p,d}∈twoCoreEdges n L G := by simpa only [fc] using edge
    rcases degree_two_neighbor_cases n L G p q c dp pq pc qc d edge' with h|h
    · exact ⟨by simpa only [h] using rq,Or.inl (by simpa only [h] using (show ordinaryDegree n L G q=2 ∧
        coreDegree n L G q=2 ∧ markedCount n L hL hn tri ht q=0 from ⟨aq,dq,mq⟩))⟩
    · exact ⟨by simpa only [h] using rc,Or.inr (by simpa only [h] using full)⟩
  exact UpperOpenMathNormalizedActualFull.certificate_normalized_neighbor_not_full n L hL hn tri hi ht f df
    neighbors c hc (by simpa only [fc] using pc) full

#print axioms certificate_balanced_pair_next_to_full_impossible
end Kobon.UpperOpenMathBalancedFullBridge
