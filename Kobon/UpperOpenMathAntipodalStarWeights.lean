import Kobon.UpperOpenMathAntipodalStarDegree
import Kobon.UpperOpenMathNormalizedPairFull

/-! Adjacent outer cores of a full antipodal star cannot both have zero
curvature. Their positive contributions occur in units of at least two. -/
namespace Kobon.UpperOpenMathAntipodalStarWeights
open Cells FanGeometry UpperFan UpperVertexBudget UpperTriangleIncidence UpperSharedIncidence
  UpperCoreExtraction UpperOpenMathCapHeavyTriples UpperOpenMathCoreComponents
  UpperOpenMathAntipodalTwoCapChart UpperOpenMathAntipodalStarDegree
  UpperOpenMathTripleCharts UpperOpenMathTwoTwoCore Finset
set_option maxHeartbeats 1000000

theorem certificate_outer_weight {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (triples : ∀ p∈core n L, (supports n L p).card=3)
    (f : UpperFan.Sectors n 3 L)
    (data : AntipodalData (fun a => ofPredicate n L (tri a) hL (ht a)) f)
    (P : Finset Point) (sub : P⊆core n L) (hc : f.center∈P) (small : P.card≤5)
    (closed : SharedCoreClosed n L (fun a => ofPredicate n L (tri a) hL (ht a)) P)
    (centerA : ordinaryDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) f.center=2)
    (z : ZMod (2*3)) (hz : z∈f.coreShared) :
    let G := fun a => ofPredicate n L (tri a) hL (ht a)
    let a := ordinaryDegree n L G (f.point z)
    let d := coreDegree n L G (f.point z)
    (6-2*(a : ℤ)-d=0 ∨ 2≤6-2*(a : ℤ)-d) ∧
      (6-2*(a : ℤ)-d=0 → a=2 ∧ d=2) := by
  classical
  let G := fun a => ofPredicate n L (tri a) hL (ht a)
  let p := f.point z
  have hp := data.core_endpoint z hz
  have degree := certificate_outer_degrees n L hL tri ht f data P hc small closed z hz
  have ordinary := UpperOpenMathDegreeBudgets.certificate_local_degree_two n L hL hn tri hi ht p hp degree
  rw [triples p hp] at ordinary
  change ordinaryDegree n L G p≤2 at ordinary
  change coreDegree n L G p≤2 at degree
  have noPartial : ¬(ordinaryDegree n L G p=2 ∧ coreDegree n L G p=1) := by
    intro partialCase
    have edge : {p,f.center}∈twoCoreEdges n L G := by
      simpa only [p,pair_comm] using UpperOpenMathAntipodalTwoCapChart.core_edge_of_label G f data.toFullData z hz
    have poor := UpperOpenMathMarkedPoverty.certificate_cap_heavy_neighbor_sum
      n L hL hn tri hi ht p f.center hp (sub hc) (triples p hp) (triples f.center (sub hc))
      (Or.inr partialCase) edge
    rw [centerA] at poor
    omega
  change (6-2*(ordinaryDegree n L G p : ℤ)-coreDegree n L G p=0 ∨
    2≤6-2*(ordinaryDegree n L G p : ℤ)-coreDegree n L G p) ∧
      (6-2*(ordinaryDegree n L G p : ℤ)-coreDegree n L G p=0 →
        ordinaryDegree n L G p=2 ∧ coreDegree n L G p=2)
  omega

theorem certificate_first_pair_not_zero_local {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (P : Finset Point) (triples : ∀ p∈P, (supports n L p).card=3)
    (f : UpperFan.Sectors n 3 L)
    (data : AntipodalData (fun a => ofPredicate n L (tri a) hL (ht a)) f)
    (sub : P⊆core n L) (hc : f.center∈P) (small : P.card≤5)
    (closed : SharedCoreClosed n L (fun a => ofPredicate n L (tri a) hL (ht a)) P)
    (centerA : ordinaryDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) f.center=2)
    (oneA : ordinaryDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) (f.point 1)=2)
    (oneD : coreDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) (f.point 1)=2)
    (twoA : ordinaryDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) (f.point 2)=2)
    (twoD : coreDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) (f.point 2)=2) : False := by
  classical
  let G := fun a => ofPredicate n L (tri a) hL (ht a)
  have oneCore : (1 : ZMod (2*3))∈f.coreShared := by rw [data.core_eq]; simp
  have twoCore : (2 : ZMod (2*3))∈f.coreShared := by rw [data.core_eq]; simp
  have h1 := data.core_endpoint 1 oneCore
  have h2 := data.core_endpoint 2 twoCore
  have p1 : f.point 1∈P := closed {f.center,f.point 1}
    (UpperOpenMathAntipodalTwoCapChart.core_edge_of_label G f data.toFullData 1 oneCore)
    f.center (by simp) hc (by simp)
  have p2 : f.point 2∈P := closed {f.center,f.point 2}
    (UpperOpenMathAntipodalTwoCapChart.core_edge_of_label G f data.toFullData 2 twoCore)
    f.center (by simp) hc (by simp)
  obtain ⟨neighbors1,neighbors2⟩ := certificate_first_neighbors n L hL tri ht f data P hc small closed
  have ng1 (q : Point) (hq : q∈core n L) (edge : {f.point 1,q}∈twoCoreEdges n L G) :
      (supports n L q).card=3 ∧ ordinaryDegree n L G q=2 := by
    have qp : q∈P := closed {f.point 1,q} edge (f.point 1) (by simp) p1 (by simp)
    refine ⟨triples q qp,?_⟩
    rcases neighbors1 q edge with h|h
    · simpa only [h] using centerA
    · simpa only [h] using twoA
  have ng2 (q : Point) (hq : q∈core n L) (edge : {f.point 2,q}∈twoCoreEdges n L G) :
      (supports n L q).card=3 ∧ ordinaryDegree n L G q=2 := by
    have qp : q∈P := closed {f.point 2,q} edge (f.point 2) (by simp) p2 (by simp)
    refine ⟨triples q qp,?_⟩
    rcases neighbors2 q edge with h|h
    · simpa only [h] using centerA
    · simpa only [h] using oneA
  obtain ⟨g,gc,dg⟩ := certificate_local_normalized_chart n L hL hn tri hi ht
    (f.point 1) h1 (triples _ p1) oneA oneD ng1
  obtain ⟨h,hh,dh⟩ := certificate_local_normalized_chart n L hL hn tri hi ht
    (f.point 2) h2 (triples _ p2) twoA twoD ng2
  have disjoint : Pairwise (fun a b => Disjoint (G a).interior (G b).interior) := by
    intro a b hab
    exact distinct_interiors_disjoint n L _ _ hL (ht a) (ht b) (fun he => hab (hi he))
  have e1 := core_edge_of_label G f data.toFullData 1 oneCore
  have rev1 : {g.center,f.center}∈twoCoreEdges n L G := by simpa only [gc,pair_comm] using e1
  obtain ⟨z,gz,gp⟩ := reverse_core_label G g dg.toChartData f.center
    (by rw [gc]; exact (data.noncentral 1).symm) rev1
  have matching := UpperOpenMathNormalizedPairFull.retained_matching_general G disjoint
    (by decide : 2≤3) g f dg.toChartData data.injective data.noncentral data.positive data.occurrences
    z 1 gz oneCore gp.symm gc.symm
  have ztwo : z=2 := by
    have cases : z=1 ∨ z=2 := by simpa only [dg.core_eq,mem_insert,mem_singleton] using gz
    rcases cases with z1|z2
    · have ord : OrdinaryAt n L (g.point 0) :=
        ((g.mem_ordinaryShared 0).mp (by rw [dg.ordinary_eq]; simp)).2.2
      have eq : f.point 2=g.point 0 := by
        have iz : (1 : ZMod (2*3))-1=0 := by decide
        have ifi : (1 : ZMod (2*3))+1=2 := by decide
        simpa only [z1,iz,ifi] using matching.2
      exact False.elim ((mem_filter.mp h2).2 (eq.symm ▸ ord))
    · exact z2
  have gtwo : g.point 2=f.center := by simpa only [ztwo] using gp
  have gone : g.point 1=h.center := by
    have iz : (2 : ZMod (2*3))-1=1 := by decide
    have ifi : (1 : ZMod (2*3))+1=2 := by decide
    have eq : f.point 2=g.point 1 := by simpa only [ztwo,iz,ifi] using matching.2
    exact eq.symm.trans hh.symm
  have g1 : (1 : ZMod (2*3))∈g.coreShared := by rw [dg.core_eq]; simp
  have gh := UpperOpenMathTwoTwoCore.core_edge_of_label G g dg.toChartData 1 g1
  have rev : {h.center,g.center}∈twoCoreEdges n L G := by simpa only [gone,pair_comm] using gh
  obtain ⟨w,hw,hp⟩ := reverse_core_label G h dh.toChartData g.center
    (by rw [← gone]; exact (dg.noncentral 1).symm) rev
  exact UpperOpenMathNormalizedPairFull.normalized_pair_full_third_impossible G disjoint hL
    g h f dg dh data.injective data.noncentral data.positive data.occurrences data.triangular_eq
    w 1 hw oneCore gone.symm hp gtwo.symm gc.symm

theorem certificate_first_pair_not_zero {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (triples : ∀ p∈core n L, (supports n L p).card=3)
    (f : UpperFan.Sectors n 3 L)
    (data : AntipodalData (fun a => ofPredicate n L (tri a) hL (ht a)) f)
    (P : Finset Point) (sub : P⊆core n L) (hc : f.center∈P) (small : P.card≤5)
    (closed : SharedCoreClosed n L (fun a => ofPredicate n L (tri a) hL (ht a)) P)
    (centerA : ordinaryDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) f.center=2)
    (oneA : ordinaryDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) (f.point 1)=2)
    (oneD : coreDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) (f.point 1)=2)
    (twoA : ordinaryDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) (f.point 2)=2)
    (twoD : coreDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) (f.point 2)=2) : False :=
  certificate_first_pair_not_zero_local n L hL hn tri hi ht P (fun p hp => triples p (sub hp))
    f data sub hc small closed centerA oneA oneD twoA twoD

theorem certificate_first_pair_weight {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (triples : ∀ p∈core n L, (supports n L p).card=3)
    (f : UpperFan.Sectors n 3 L)
    (data : AntipodalData (fun a => ofPredicate n L (tri a) hL (ht a)) f)
    (P : Finset Point) (sub : P⊆core n L) (hc : f.center∈P) (small : P.card≤5)
    (closed : SharedCoreClosed n L (fun a => ofPredicate n L (tri a) hL (ht a)) P)
    (centerA : ordinaryDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) f.center=2) :
    let G := fun a => ofPredicate n L (tri a) hL (ht a)
    2≤(6-2*(ordinaryDegree n L G (f.point 1) : ℤ)-coreDegree n L G (f.point 1))+
      (6-2*(ordinaryDegree n L G (f.point 2) : ℤ)-coreDegree n L G (f.point 2)) := by
  have one := certificate_outer_weight n L hL hn tri hi ht triples f data P sub hc small closed centerA
    1 (by rw [data.core_eq]; simp)
  have two := certificate_outer_weight n L hL hn tri hi ht triples f data P sub hc small closed centerA
    2 (by rw [data.core_eq]; simp)
  dsimp only at one two ⊢
  by_cases zero1 : 6-2*(ordinaryDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) (f.point 1) : ℤ)-
      coreDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) (f.point 1)=0
  · have typ1 := one.2 zero1
    by_cases zero2 : 6-2*(ordinaryDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) (f.point 2) : ℤ)-
        coreDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) (f.point 2)=0
    · have typ2 := two.2 zero2
      exact False.elim (certificate_first_pair_not_zero n L hL hn tri hi ht triples f data P sub hc small closed
        centerA typ1.1 typ1.2 typ2.1 typ2.2)
    · omega
  · omega

#print axioms certificate_outer_weight
#print axioms certificate_first_pair_not_zero
#print axioms certificate_first_pair_weight
end Kobon.UpperOpenMathAntipodalStarWeights
