import Kobon.UpperOpenMathMarkedPorts
import Kobon.UpperOpenMathMarkedFanShapes
import Kobon.UpperOpenMathAntipodalEscape

/-! Actual port geometry used by the sharp marked-curvature zero case. -/
namespace Kobon.UpperOpenMathMarkedZeroGeometry
open Cells FanGeometry UpperFan UpperVertexBudget UpperTriangleIncidence UpperSharedIncidence
  UpperCoreExtraction UpperOpenMathCapHeavyTriples UpperOpenMathCoreComponents
  UpperOpenMathActualFans UpperOpenMathRadialOrder UpperOpenMathMarkedPorts
  UpperOpenMathTripleCharts UpperOpenMathAntipodalEscape Finset
open scoped BigOperators

theorem nonordinary_port_not_marked {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (ht : ∀ a, TrianglePredicate n L (tri a))
    (c : Point) (hc : c∈core n L) [NeZero (2*(supports n L c).card)]
    (w : ZMod (2*(supports n L c).card))
    (np : ¬OrdinaryAt n L ((atCoreFan n L hL hn tri ht c hc).point (w-1))) :
    {c,(atCoreFan n L hL hn tri ht c hc).point w}∉markedEdges n L hL hn tri ht c := by
  classical
  intro he
  let f := atCoreFan n L hL hn tri ht c hc
  obtain ⟨z,hzc,hprev,hnext,heq⟩ := marked_edge_ray n L hL hn tri ht c hc _ he
  have inj := pair_map_injective c f.point
    (fan_point_injective n L hL hn tri ht c (mem_filter.mp hc).1 (atPoint n L hL hn c) (by
      have := core_multiplicity n L hL hc; omega))
    (fan_point_ne_center n L hL hn tri ht c (mem_filter.mp hc).1 (atPoint n L hL hn c) (by
      have := core_multiplicity n L hL hc; omega))
  have zw : z=w := inj heq.symm
  have ho := ((f.mem_ordinaryShared (z-1)).mp hprev).2.2
  exact np (by simpa only [zw] using ho)

theorem normalized_nonordinary_port_not_adjacent {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (f : UpperFan.Sectors n 3 L) (df : NormalizedData (fun a => ofPredicate n L (tri a) hL (ht a)) f)
    (c : Point) (hc : c∈core n L) [NeZero (2*(supports n L c).card)]
    (w : ZMod (2*(supports n L c).card))
    (wc : w∈(atCoreFan n L hL hn tri ht c hc).coreShared)
    (wp : (atCoreFan n L hL hn tri ht c hc).point w=f.center)
    (np : ¬OrdinaryAt n L ((atCoreFan n L hL hn tri ht c hc).point (w-1)))
    (nn : ¬OrdinaryAt n L ((atCoreFan n L hL hn tri ht c hc).point (w+1))) : False := by
  classical
  let G := fun a => ofPredicate n L (tri a) hL (ht a)
  let D := atPoint n L hL hn c
  let g := atCoreFan n L hL hn tri ht c hc
  have hr := core_multiplicity n L hL hc
  have edge := (fan_core_iff n L hL hn tri ht c (mem_filter.mp hc).1 D (by omega) hi hc w).mp wc
  change {c,g.point w}∈twoCoreEdges n L G at edge
  change g.point w=f.center at wp
  have rev : {f.center,c}∈twoCoreEdges n L G := by simpa only [wp,pair_comm] using edge
  have hne : c≠f.center := by
    have hh : g.point w≠c := fan_point_ne_center n L hL hn tri ht c (mem_filter.mp hc).1 D (by omega) w
    simpa only [wp] using Ne.symm hh
  obtain ⟨z,fz,fp⟩ := UpperOpenMathTwoTwoCore.reverse_core_label G f df.toChartData c hne rev
  have disjoint : Pairwise (fun a b => Disjoint (G a).interior (G b).interior) := by
    intro a b hab
    exact distinct_interiors_disjoint n L _ _ hL (ht a) (ht b) (fun h => hab (hi h))
  have actual : ∀ z∈g.triangular, Nonempty (UpperOpenMathSectorRecords.Occurrence G g.center g.point z) := by
    intro z hz
    exact (UpperOpenMathSectorRecords.mem_triangular G c g.point z).mp hz
  exact UpperOpenMathMarkedFanShapes.normalized_nonordinary_neighbors_incompatible G disjoint (by omega)
    f g df
    (fan_point_injective n L hL hn tri ht c (mem_filter.mp hc).1 D (by omega))
    (fan_point_ne_center n L hL hn tri ht c (mem_filter.mp hc).1 D (by omega))
    (fan_positive n L hL hn tri ht c (mem_filter.mp hc).1 D (by omega)) actual z w fz wc fp.symm wp np nn

theorem marked_poor_antipodal_neighbor {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (triples : ∀ p∈core n L, (supports n L p).card=3)
    (p b : Point) (hp : p∈core n L) (hb : b∈core n L)
    (edge : {p,b}∈markedEdges n L hL hn tri ht p) (bne : b≠p)
    (ba : ordinaryDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) b=0)
    (bd : coreDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) b=2) :
    ∃ u∈core n L, {b,u}∈twoCoreEdges n L (fun a => ofPredicate n L (tri a) hL (ht a)) ∧
      ∃ k : ℝ, 0<k ∧ u=oppositePoint b p k := by
  classical
  have rp := triples p hp
  have rb := triples b hb
  letI : NeZero (2*(supports n L p).card) := ⟨by omega⟩
  letI : NeZero (2*(supports n L b).card) := ⟨by omega⟩
  let D := atPoint n L hL hn p
  let E := atPoint n L hL hn b
  let f := atCoreFan n L hL hn tri ht p hp
  let g := atCoreFan n L hL hn tri ht b hb
  obtain ⟨z,hzc,hprev,hnext,he⟩ := marked_edge_ray n L hL hn tri ht p hp {p,b} edge
  have bpoint : b=f.point z := by
    have hm : b∈({p,f.point z} : Edge) := by rw [← he]; simp
    rcases mem_insert.mp hm with hm|hm
    · exact False.elim (bne hm)
    · exact mem_singleton.mp hm
  obtain ⟨w,wc,wp,right,left⟩ := UpperOpenMathActualMatching.certificate_neighbor_matching
    n L hL hn tri hi ht p b hp hb D E (by omega) (by omega) z hzc bpoint
  change w∈g.coreShared at wc
  change g.point w=p at wp
  change g.point (w-1)=f.point (z+1) at right
  change g.point (w+1)=f.point (z-1) at left
  have op : OrdinaryAt n L (g.point (w-1)) := by
    rw [right]
    exact ((f.mem_ordinaryShared (z+1)).mp hnext).2.2
  have on : OrdinaryAt n L (g.point (w+1)) := by
    rw [left]
    exact ((f.mem_ordinaryShared (z-1)).mp hprev).2.2
  have ga : g.ordinaryShared.card=0 := (at_core_ordinary_card n L hL hn tri hi ht b hb).trans ba
  have gd : g.coreShared.card=2 := (at_core_core_card n L hL hn tri hi ht b hb).trans bd
  have opposite := UpperOpenMathMarkedFanShapes.poor_antipodal_core_card rb g ga gd w wc op on
  have uc := fan_core_endpoint n L hL hn tri ht b (mem_filter.mp hb).1 E (by omega) hi hb (w+3) opposite
  have ue := (fan_core_iff n L hL hn tri ht b (mem_filter.mp hb).1 E (by omega) hi hb (w+3)).mp opposite
  obtain ⟨k,hk,hu⟩ := g.antipodal w
  have index : w+((supports n L b).card : ZMod (2*(supports n L b).card))=w+3 :=
    congrArg (fun t : ℕ => w+(t : ZMod (2*(supports n L b).card))) rb
  rw [index,wp] at hu
  change g.point (w+3)=(b.1-k*(p.1-b.1),b.2-k*(p.2-b.2)) at hu
  exact ⟨g.point (w+3),uc,ue,k,hk,hu⟩

theorem unmarked_target_not_poor {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (triples : ∀ p∈core n L, (supports n L p).card=3)
    (P : Finset Point) (sub : P⊆core n L)
    (closed : SharedCoreClosed n L (fun a => ofPredicate n L (tri a) hL (ht a)) P)
    (tight : (∑ p∈P, markedCount n L hL hn tri ht p)=
      ∑ p∈P.filter (fun p => ordinaryDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) p≤1 ∧
        ordinaryDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) p+
          coreDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) p≤2),
        coreDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) p)
    (p b : Point) (hb : b∈P)
    (poor : ordinaryDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) b≤1 ∧
      ordinaryDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) b+
        coreDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) b≤2)
    (edge : {p,b}∈twoCoreEdges n L (fun a => ofPredicate n L (tri a) hL (ht a)))
    (notMarked : {p,b}∉markedEdges n L hL hn tri ht p) : False := by
  classical
  obtain ⟨s,hs,hsb,marked⟩ := tight_marked_edge_coverage n L hL hn tri hi ht triples P sub closed tight
    b (mem_filter.mpr ⟨hb,poor⟩) {p,b} edge (by simp)
  have spec := marked_edge_spec n L hL hn tri hi ht triples s (sub hs) {p,b} marked
  have sp : s=p := by
    rcases mem_insert.mp spec.2.1 with he|he
    · exact he
    · exact False.elim (hsb (mem_singleton.mp he))
  exact notMarked (by simpa only [sp] using marked)

#print axioms normalized_nonordinary_port_not_adjacent
#print axioms marked_poor_antipodal_neighbor
#print axioms unmarked_target_not_poor
end Kobon.UpperOpenMathMarkedZeroGeometry
