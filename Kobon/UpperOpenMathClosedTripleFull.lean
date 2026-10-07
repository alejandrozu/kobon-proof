import Kobon.UpperOpenMathClosedHighSharing
import Kobon.UpperOpenMathNormalizedActualFull
import Kobon.UpperOpenMathClosedFullSharing

/-! A nonempty closed set cannot consist of balanced triple cores and full
triple cores. The multiplicity assumption is local to this closed set. -/
namespace Kobon.UpperOpenMathClosedTripleFull
open Cells FanGeometry UpperFan UpperVertexBudget UpperTriangleIncidence UpperSharedIncidence
  UpperCoreExtraction UpperOpenMathCapHeavyTriples UpperOpenMathCoreComponents
  UpperOpenMathTripleCharts UpperOpenMathMarkedPorts Finset
set_option maxHeartbeats 1000000

theorem certificate_closed_triple_two_or_full_impossible {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (P : Finset Point) (sub : P⊆core n L) (nonempty : P.Nonempty)
    (closed : SharedCoreClosed n L (fun a => ofPredicate n L (tri a) hL (ht a)) P)
    (triples : ∀ p∈P, (supports n L p).card=3)
    (rigid : ∀ p∈P,
      (ordinaryDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) p=2 ∧
       coreDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) p=2) ∨
      ordinaryDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) p+
        coreDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) p=6) : False := by
  classical
  let G := fun a => ofPredicate n L (tri a) hL (ht a)
  let R := P.filter (fun p => ordinaryDegree n L G p=2 ∧ coreDegree n L G p=2)
  have high (p : Point) (hp : p∈P) : 3≤ordinaryDegree n L G p+coreDegree n L G p := by
    have hh := rigid p hp
    change (ordinaryDegree n L G p=2 ∧ coreDegree n L G p=2) ∨
      ordinaryDegree n L G p+coreDegree n L G p=6 at hh
    rcases hh with hh|hh <;> omega
  have zero (p : Point) (hp : p∈P) : markedCount n L hL hn tri ht p=0 :=
    UpperOpenMathClosedHighSharing.certificate_closed_high_zero_marks
      n L hL hn tri hi ht P sub closed triples high p hp
  have norm (p : Point) (hp : p∈R) : ∃ f : UpperFan.Sectors n 3 L,
      f.center=p ∧ NormalizedData G f := by
    obtain ⟨hpP,ha,hd⟩ := mem_filter.mp hp
    exact certificate_normalized_two_two_of_zero_marks n L hL hn tri hi ht p (sub hpP)
      (triples p hpP) ha hd (zero p hpP)
  have rclosed : SharedCoreClosed n L G R := by
    intro e he p hpe hpR q hqe
    have hpP := (mem_filter.mp hpR).1
    have hqP : q∈P := closed e he p hpe hpP hqe
    rcases rigid q hqP with balance|full
    · exact mem_filter.mpr ⟨hqP,balance⟩
    · by_cases hqp : q=p
      · obtain ⟨_,ha,hd⟩ := mem_filter.mp hpR
        change ordinaryDegree n L G p=2 at ha
        change coreDegree n L G p=2 at hd
        rw [hqp] at full
        change ordinaryDegree n L G p+coreDegree n L G p=6 at full
        omega
      have pair : e={p,q} := by
        apply Eq.symm
        apply eq_of_subset_of_card_le
        · intro x hx
          rcases mem_insert.mp hx with rfl|hx
          · exact hpe
          · simpa only [mem_singleton.mp hx] using hqe
        · rw [card_pair (fun h => hqp h.symm),used_edge_card G (mem_filter.mp (mem_sdiff.mp he).1).1]
      obtain ⟨f,fc,df⟩ := norm p hpR
      apply False.elim
      apply UpperOpenMathNormalizedActualFull.certificate_normalized_neighbor_not_full
        n L hL hn tri hi ht f df ?_ q (sub hqP) (by simpa only [fc,pair] using he) full
      intro d hd edge
      have hdP : d∈P := closed {f.center,d} edge f.center (by simp)
        (by simpa only [fc] using hpP) (by simp)
      refine ⟨triples d hdP,?_⟩
      rcases rigid d hdP with hd|hd
      · exact Or.inl ⟨hd.1,hd.2,zero d hdP⟩
      · exact Or.inr hd
  by_cases rnonempty : R.Nonempty
  · apply UpperOpenMathTwoTwoCore.certificate_closed_two_two_impossible
      n L hL hn tri hi ht R ((filter_subset _ _).trans sub) rnonempty rclosed
    intro p hp
    obtain ⟨hpP,ha,hd⟩ := mem_filter.mp hp
    exact ⟨triples p hpP,ha,hd⟩
  · have rempty : R=∅ := not_nonempty_iff_eq_empty.mp rnonempty
    apply UpperOpenMathClosedFullSharing.certificate_closed_full_sharing_impossible
      n L hL hn tri hi ht P sub nonempty closed
    intro p hp
    have full : ordinaryDegree n L G p+coreDegree n L G p=6 := by
      rcases rigid p hp with hpR|hpF
      · have hm : p∈R := mem_filter.mpr ⟨hp,hpR⟩
        rw [rempty] at hm
        exact False.elim (notMem_empty p hm)
      · exact hpF
    rw [triples p hp]
    exact full

#print axioms certificate_closed_triple_two_or_full_impossible
end Kobon.UpperOpenMathClosedTripleFull
