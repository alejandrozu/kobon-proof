import Kobon.UpperOpenMathMarkedPorts
import Kobon.UpperOpenMathFullSharing
import Kobon.UpperOpenMathTwoCapNeighborRigidity

/-! Source-preserving charts for every full triple fan, independent of its
ordinary/core split. -/
namespace Kobon.UpperOpenMathFullTripleChart
open Cells FanGeometry UpperFan UpperVertexBudget UpperTriangleIncidence UpperSharedIncidence
  UpperCoreExtraction UpperOpenMathCapHeavyTriples UpperOpenMathActualFans
  UpperOpenMathRadialOrder UpperOpenMathMarkedPorts UpperOpenMathTripleCharts Finset

structure FullOriginalData {α : Type*} [Fintype α] (G : α → TriangleGeometry)
    {n : ℕ} {L : ℕ → Line ℝ} (f : UpperFan.Sectors n 3 L) : Prop where
  injective : Function.Injective f.point
  noncentral : ∀ z, f.point z≠f.center
  positive : ∀ z, 0<areaDet f.center (f.point z) (f.point (z+1))
  core_endpoint : ∀ z∈f.coreShared, f.point z∈core n L
  core_image : f.coreShared.image (fun z => ({f.center,f.point z} : Edge))=
    (twoCoreEdges n L G).filter (fun e => f.center∈e)
  occurrences : ∀ z∈f.triangular,
    Nonempty (UpperOpenMathSectorRecords.Occurrence G f.center f.point z)
  full : f.triangular=univ

theorem lift_full_three {α : Type*} [Fintype α] (G : α → TriangleGeometry)
    {n r : ℕ} [NeZero (2*r)] {L : ℕ → Line ℝ} (hr : r=3)
    (f : UpperFan.Sectors n r L)
    (inj : Function.Injective f.point) (nc : ∀ z, f.point z≠f.center)
    (pos : ∀ z, 0<areaDet f.center (f.point z) (f.point (z+1)))
    (ce : ∀ z∈f.coreShared, f.point z∈core n L)
    (im : f.coreShared.image (fun z => ({f.center,f.point z} : Edge))=
      (twoCoreEdges n L G).filter (fun e => f.center∈e))
    (occ : ∀ z∈f.triangular, Nonempty (UpperOpenMathSectorRecords.Occurrence G f.center f.point z))
    (full : f.triangular=univ) :
    ∃ g : UpperFan.Sectors n 3 L, g.center=f.center ∧ FullOriginalData G g := by
  subst r
  exact ⟨f,rfl,⟨inj,nc,pos,ce,im,occ,full⟩⟩

theorem certificate_full_triple_chart {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (c : Point) (hc : c∈core n L) (rc : (supports n L c).card=3)
    (total : ordinaryDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) c+
      coreDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) c=6) :
    ∃ f : UpperFan.Sectors n 3 L, f.center=c ∧
      FullOriginalData (fun a => ofPredicate n L (tri a) hL (ht a)) f := by
  classical
  let G := fun a => ofPredicate n L (tri a) hL (ht a)
  letI : NeZero (2*(supports n L c).card) := ⟨by omega⟩
  let D := atPoint n L hL hn c
  let f := atCoreFan n L hL hn tri ht c hc
  have ordinary := at_core_ordinary_card n L hL hn tri hi ht c hc
  have degree := at_core_core_card n L hL hn tri hi ht c hc
  have split := f.shared_card_split
  have full : f.triangular=univ := by
    have card : f.shared.card=2*(supports n L c).card := by
      rw [← split,ordinary,degree,total,rc]
    exact UpperOpenMathFullSharing.shared_full f card
  have ce : ∀ z∈f.coreShared, f.point z∈core n L :=
    fan_core_endpoint n L hL hn tri ht c (mem_filter.mp hc).1 D (by omega) hi hc
  have im : f.coreShared.image (fun z => ({f.center,f.point z} : Edge))=
      (twoCoreEdges n L G).filter (fun e => f.center∈e) :=
    fan_core_image n L hL hn tri ht c (mem_filter.mp hc).1 D (by omega) hi hc
  have occ : ∀ z∈f.triangular, Nonempty
      (UpperOpenMathSectorRecords.Occurrence G f.center f.point z) := by
    intro z hz
    exact (UpperOpenMathSectorRecords.mem_triangular G c f.point z).mp hz
  exact lift_full_three G rc f
    (fan_point_injective n L hL hn tri ht c (mem_filter.mp hc).1 D (by omega))
    (fan_point_ne_center n L hL hn tri ht c (mem_filter.mp hc).1 D (by omega))
    (fan_positive n L hL hn tri ht c (mem_filter.mp hc).1 D (by omega)) ce im occ full

theorem normalized_two_or_full_neighbors_no_full {α : Type*} [Fintype α]
    (G : α → TriangleGeometry)
    (disjoint : Pairwise (fun a b => Disjoint (G a).interior (G b).interior))
    {n : ℕ} {L : ℕ → Line ℝ} (hL : NoParallel n L)
    (f g k : UpperFan.Sectors n 3 L) (df : NormalizedData G f)
    (dg : NormalizedData G g ∨ FullOriginalData G g)
    (dk : NormalizedData G k ∨ FullOriginalData G k)
    (w x : ZMod (2*3)) (gw : w∈g.coreShared) (kx : x∈k.coreShared)
    (gc : g.center=f.point 1) (gp : g.point w=f.center)
    (kc : k.center=f.point 2) (kp : k.point x=f.center)
    (full : FullOriginalData G g ∨ FullOriginalData G k) : False := by
  classical
  have f1 : (1 : ZMod (2*3))∈f.coreShared := by rw [df.core_eq]; simp
  have f2 : (2 : ZMod (2*3))∈f.coreShared := by rw [df.core_eq]; simp
  rcases dg with dg|dg <;> rcases dk with dk|dk
  · rcases full with fg|fk
    · have shared := fg.full
      have split := g.shared_card_split
      rw [dg.ordinary_card,dg.core_card] at split
      have fullCard : g.shared.card=6 := by simp [UpperFan.Sectors.shared,shared]
      omega
    · have shared := fk.full
      have split := k.shared_card_split
      rw [dk.ordinary_card,dk.core_card] at split
      have fullCard : k.shared.card=6 := by simp [UpperFan.Sectors.shared,shared]
      omega
  · exact UpperOpenMathNormalizedPairFull.normalized_pair_full_third_impossible
      G disjoint hL f g k df dg dk.injective dk.noncentral dk.positive dk.occurrences
      dk.full w x gw kx gc gp kc kp
  · exact UpperOpenMathNormalizedPairFullSwap.normalized_swapped_pair_full_third_impossible
      G disjoint hL f k g df dk dg.injective dg.noncentral dg.positive dg.occurrences
      dg.full x w kx gw kc kp gc gp
  · have fg := UpperOpenMathNormalizedPairFull.retained_matching_general G disjoint
      (by decide : 2≤3) f g df.toChartData dg.injective dg.noncentral dg.positive dg.occurrences
      1 w f1 gw gc gp
    have fk := UpperOpenMathNormalizedPairFull.retained_matching_general G disjoint
      (by decide : 2≤3) f k df.toChartData dk.injective dk.noncentral dk.positive dk.occurrences
      2 x f2 kx kc kp
    have h11 : (1 : ZMod (2*3))-1=0 := by decide
    have h12 : (1 : ZMod (2*3))+1=2 := by decide
    have h21 : (2 : ZMod (2*3))-1=1 := by decide
    have h23 : (2 : ZMod (2*3))+1=3 := by decide
    exact UpperOpenMathNormalizedFullNeighbors.normalized_full_neighbors_impossible G hL
      f g k df dg.full dk.full dg.noncentral w x gc gp
      (by simpa only [h12] using fg.1) (by simpa only [h11] using fg.2) kc kp
      (by simpa only [h23] using fk.1) (by simpa only [h21] using fk.2)

#print axioms certificate_full_triple_chart
#print axioms normalized_two_or_full_neighbors_no_full
end Kobon.UpperOpenMathFullTripleChart
