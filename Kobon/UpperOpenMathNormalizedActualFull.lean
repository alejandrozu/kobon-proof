import Kobon.UpperOpenMathFullTripleChart

/-! Actual normalized balanced triple fans cannot touch a full triple fan
when all their shared-core neighbours are balanced and unmarked or full.
Only neighbouring cores are restricted; other cores may have any order. -/
namespace Kobon.UpperOpenMathNormalizedActualFull
open Cells FanGeometry UpperFan UpperVertexBudget UpperTriangleIncidence UpperSharedIncidence
  UpperCoreExtraction UpperOpenMathCapHeavyTriples UpperOpenMathCoreComponents
  UpperOpenMathTripleCharts UpperOpenMathTwoTwoCore UpperOpenMathFullTripleChart
  UpperOpenMathMarkedPorts Finset
set_option maxHeartbeats 1000000

theorem certificate_normalized_neighbor_not_full {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (f : UpperFan.Sectors n 3 L)
    (df : NormalizedData (fun a => ofPredicate n L (tri a) hL (ht a)) f)
    (neighbors : ∀ p∈core n L,
      {f.center,p}∈twoCoreEdges n L (fun a => ofPredicate n L (tri a) hL (ht a)) →
      (supports n L p).card=3 ∧
      ((ordinaryDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) p=2 ∧
        coreDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) p=2 ∧
        markedCount n L hL hn tri ht p=0) ∨
       ordinaryDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) p+
         coreDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) p=6))
    (d : Point) (hd : d∈core n L)
    (edge : {f.center,d}∈twoCoreEdges n L (fun a => ofPredicate n L (tri a) hL (ht a)))
    (full : ordinaryDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) d+
      coreDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) d=6) : False := by
  classical
  let G := fun a => ofPredicate n L (tri a) hL (ht a)
  have disjoint : Pairwise (fun a b => Disjoint (G a).interior (G b).interior) := by
    intro a b hab
    exact distinct_interiors_disjoint n L _ _ hL (ht a) (ht b) (fun he => hab (hi he))
  have chart (p : Point) (hp : p∈core n L) (pe : {f.center,p}∈twoCoreEdges n L G) :
      ∃ g : UpperFan.Sectors n 3 L, g.center=p ∧
        (NormalizedData G g ∨ FullOriginalData G g) ∧
        (ordinaryDegree n L G p+coreDegree n L G p=6 → FullOriginalData G g) := by
    obtain ⟨rp,cases⟩ := neighbors p hp pe
    rcases cases with ⟨ap,dp,mp⟩|total
    · obtain ⟨g,gc,dg⟩ := certificate_normalized_two_two_of_zero_marks n L hL hn tri hi ht p hp rp ap dp mp
      refine ⟨g,gc,Or.inl dg,?_⟩
      intro hh
      change ordinaryDegree n L G p=2 at ap
      change coreDegree n L G p=2 at dp
      omega
    · obtain ⟨g,gc,dg⟩ := certificate_full_triple_chart n L hL hn tri hi ht p hp rp total
      exact ⟨g,gc,Or.inr dg,fun _ => dg⟩
  have f1 : (1 : ZMod (2*3))∈f.coreShared := by rw [df.core_eq]; simp
  have f2 : (2 : ZMod (2*3))∈f.coreShared := by rw [df.core_eq]; simp
  obtain ⟨g,gc,dg,gfull⟩ := chart (f.point 1) (df.core_endpoint 1 f1)
    (core_edge_of_label G f df.toChartData 1 f1)
  obtain ⟨k,kc,dk,kfull⟩ := chart (f.point 2) (df.core_endpoint 2 f2)
    (core_edge_of_label G f df.toChartData 2 f2)
  have gm : g.coreShared.image (fun z => ({g.center,g.point z} : Edge))=
      (twoCoreEdges n L G).filter (fun e => g.center∈e) := by
    rcases dg with h|h <;> exact h.core_image
  have km : k.coreShared.image (fun z => ({k.center,k.point z} : Edge))=
      (twoCoreEdges n L G).filter (fun e => k.center∈e) := by
    rcases dk with h|h <;> exact h.core_image
  obtain ⟨w,gw,gp⟩ := UpperOpenMathTwoCapNeighborRigidity.reverse_label_of_image G g gm f.center
    (by rw [gc]; exact (df.noncentral 1).symm)
    (by simpa only [gc,pair_comm] using core_edge_of_label G f df.toChartData 1 f1)
  obtain ⟨x,kx,kp⟩ := UpperOpenMathTwoCapNeighborRigidity.reverse_label_of_image G k km f.center
    (by rw [kc]; exact (df.noncentral 2).symm)
    (by simpa only [kc,pair_comm] using core_edge_of_label G f df.toChartData 2 f2)
  have used := (mem_filter.mp (mem_sdiff.mp edge).1).1
  have ne : d≠f.center := by
    intro hh
    have cc := used_edge_card G used
    simp only [hh,insert_eq_of_mem (mem_singleton_self f.center),card_singleton] at cc
    omega
  obtain ⟨z,fz,fd⟩ := reverse_core_label G f df.toChartData d ne edge
  have cases : z=1 ∨ z=2 := by simpa only [df.core_eq,mem_insert,mem_singleton] using fz
  have fullChart : FullOriginalData G g ∨ FullOriginalData G k := by
    rcases cases with rfl|rfl
    · exact Or.inl (gfull (by simpa only [fd] using full))
    · exact Or.inr (kfull (by simpa only [fd] using full))
  exact normalized_two_or_full_neighbors_no_full G disjoint hL f g k df dg dk
    w x gw kx gc gp kc kp fullChart

#print axioms certificate_normalized_neighbor_not_full
end Kobon.UpperOpenMathNormalizedActualFull
