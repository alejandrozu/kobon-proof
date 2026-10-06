import Kobon.UpperOpenMathCoreComponents
import Kobon.UpperOpenMathSupportedCores

/-! A nonempty closed set of actual cores cannot consist of extremal fans. -/
namespace Kobon.UpperOpenMathClosedExtremal
open Cells FanGeometry UpperVertexBudget UpperTriangleIncidence UpperSharedIncidence
  UpperCoreExtraction UpperOpenMathCapHeavyTriples UpperOpenMathCoreComponents Finset

theorem union_closed_of_equal_endpoint_counts {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (G : α → TriangleGeometry)
    (E H : Finset Point) (disjoint : Disjoint E H)
    (equal : ∀ e∈twoCoreEdges n L G, (e∩E).card=(e∩H).card) :
    SharedCoreClosed n L G (E∪H) := by
  classical
  intro e he p hp hpUnion q hq
  have hposE : 0<(e∩E).card := by
    rcases mem_union.mp hpUnion with hpE|hpH
    · exact card_pos.mpr ⟨p,mem_inter.mpr ⟨hp,hpE⟩⟩
    · rw [equal e he]
      exact card_pos.mpr ⟨p,mem_inter.mpr ⟨hp,hpH⟩⟩
  have hposH : 0<(e∩H).card := by rw [← equal e he]; exact hposE
  obtain ⟨a,ha⟩ := card_pos.mp hposE
  obtain ⟨b,hb⟩ := card_pos.mp hposH
  obtain ⟨hae,haE⟩ := mem_inter.mp ha
  obtain ⟨hbe,hbH⟩ := mem_inter.mp hb
  have hab : a≠b := by
    intro hh
    exact disjoint_left.mp disjoint haE (by simpa only [hh] using hbH)
  have pair : e={a,b} := by
    apply Eq.symm
    apply eq_of_subset_of_card_le
    · intro x hx
      rcases mem_insert.mp hx with hx|hx
      · simpa only [hx] using hae
      · simpa only [mem_singleton.mp hx] using hbe
    · rw [card_pair hab,used_edge_card G (mem_filter.mp (mem_sdiff.mp he).1).1]
  rw [pair] at hq
  rcases mem_insert.mp hq with hq|hq
  · exact mem_union.mpr (Or.inl (by simpa only [hq] using haE))
  · exact mem_union.mpr (Or.inr (by simpa only [mem_singleton.mp hq] using hbH))

theorem certificate_closed_extremal_impossible {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (P : Finset Point) (sub : P⊆core n L) (nonempty : P.Nonempty)
    (closed : SharedCoreClosed n L (fun a => ofPredicate n L (tri a) hL (ht a)) P)
    (extremal : ∀ p∈P, ordinaryDegree n L
      (fun a => ofPredicate n L (tri a) hL (ht a)) p=2*(supports n L p).card-3) : False := by
  classical
  obtain ⟨p,hp,hmax⟩ := exists_max_image P (fun p : Point => p.1) nonempty
  let w : Line ℝ := ⟨-1,0,-p.1⟩
  have wp : affineEval w p=0 := by dsimp [w,affineEval]; ring
  have valid : w.a≠0 ∨ w.b≠0 := Or.inl (by norm_num [w])
  have hext : 2*(supports n L p).card-3≤ordinaryDegree n L
      (fun a => ofPredicate n L (tri a) hL (ht a)) p := Nat.le_of_eq (extremal p hp).symm
  obtain ⟨q,hq,edge,neg⟩ := UpperOpenMathSupportedCores.certificate_extremal_neighbors_surround
    n L hL hn tri hi ht p (sub hp) w wp valid hext
  have hqP : q∈P := closed {p,q} edge p (by simp) hp (by simp)
  have hle := hmax q hqP
  dsimp [w,affineEval] at neg
  linarith

#print axioms union_closed_of_equal_endpoint_counts
#print axioms certificate_closed_extremal_impossible
end Kobon.UpperOpenMathClosedExtremal
