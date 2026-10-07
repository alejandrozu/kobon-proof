import Kobon.UpperOpenMathQuadThreeBoundary
import Kobon.UpperOpenMathAntipodalSameNeighbors

/-! Three common core neighbors determine at most one antipodal full star.
The actual elementary sides exclude both competing boundary-pair positions
and strictly crossing cevians. No graph embedding is assumed. -/
namespace Kobon.UpperOpenMathAntipodalThreeNeighbors
open Cells FanGeometry UpperFan UpperVertexBudget UpperTriangleIncidence
  UpperSharedIncidence UpperCoreExtraction UpperOpenMathAntipodalTwoCapChart
  UpperOpenMathAntipodalCenterUniqueness UpperOpenMathAntipodalSameNeighbors
  UpperOpenMathQuadThreeBoundary UpperOpenMathCevianCrossing
  UpperOpenMathCapHeavyTriples Finset
set_option maxHeartbeats 1000000

noncomputable def AntipodalCore {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (ht : ∀ a, TrianglePredicate n L (tri a)) (c : Point) : Prop :=
  c∈core n L ∧ (supports n L c).card=3 ∧
    ordinaryDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) c=2 ∧
    coreDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) c=4 ∧
    UpperOpenMathMarkedPorts.markedCount n L hL hn tri ht c=0

theorem chart_three_boundary {α : Type*} [Fintype α]
    {n : ℕ} {L : ℕ → Line ℝ} (G : α → TriangleGeometry)
    (f : Sectors n 3 L) (df : AntipodalData G f) (p q r : Point)
    (mp : p∈f.coreShared.image f.point) (mq : q∈f.coreShared.image f.point)
    (mr : r∈f.coreShared.image f.point) (pq : p≠q) (pr : p≠r) (qr : q≠r) :
    areaDet p q r≠0 ∧ (Between f.center p q∨Between f.center p r∨Between f.center q r) := by
  have members (x : Point) (hx : x∈f.coreShared.image f.point) :
      x=f.point 1∨x=f.point 2∨x=f.point 4∨x=f.point 5 := by
    simpa only [df.core_eq,image_insert,image_singleton,mem_insert,mem_singleton] using hx
  apply three_corner_boundary f.center (f.point 1) (f.point 2) (f.point 4) (f.point 5) p q r
  · exact df.positive 1
  · simpa using antipodal_outer_between f 1
  · simpa using antipodal_outer_between f 2
  · exact members p mp
  · exact members q mq
  · exact members r mr
  · exact pq
  · exact pr
  · exact qr

/-- Other cores may have any multiplicity. -/
theorem certificate_three_common_neighbors_unique {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (c d : Point) (hc : AntipodalCore n L hL hn tri ht c)
    (hd : AntipodalCore n L hL hn tri ht d)
    (p q r : Point)
    (hp : p∈coreNeighbors n L (fun a => ofPredicate n L (tri a) hL (ht a)) c∩
      coreNeighbors n L (fun a => ofPredicate n L (tri a) hL (ht a)) d)
    (hq : q∈coreNeighbors n L (fun a => ofPredicate n L (tri a) hL (ht a)) c∩
      coreNeighbors n L (fun a => ofPredicate n L (tri a) hL (ht a)) d)
    (hr : r∈coreNeighbors n L (fun a => ofPredicate n L (tri a) hL (ht a)) c∩
      coreNeighbors n L (fun a => ofPredicate n L (tri a) hL (ht a)) d)
    (pq : p≠q) (pr : p≠r) (qr : q≠r) : c=d := by
  classical
  let G := fun a => ofPredicate n L (tri a) hL (ht a)
  obtain ⟨hcC,rc,ac,dc,mc⟩ := hc
  obtain ⟨hdC,rd,ad,dd,md⟩ := hd
  obtain ⟨f,fc,df⟩ := certificate_antipodal_chart n L hL hn tri hi ht c hcC rc ac dc mc
  obtain ⟨g,gd,dg⟩ := certificate_antipodal_chart n L hL hn tri hi ht d hdC rd ad dd md
  have fe := chart_outer_eq_neighbors n L G f df
  have ge := chart_outer_eq_neighbors n L G g dg
  rw [fc] at fe
  rw [gd] at ge
  have cp : p∈f.coreShared.image f.point := by rw [fe]; exact (mem_inter.mp hp).1
  have cq : q∈f.coreShared.image f.point := by rw [fe]; exact (mem_inter.mp hq).1
  have cr : r∈f.coreShared.image f.point := by rw [fe]; exact (mem_inter.mp hr).1
  have dp : p∈g.coreShared.image g.point := by rw [ge]; exact (mem_inter.mp hp).2
  have dq : q∈g.coreShared.image g.point := by rw [ge]; exact (mem_inter.mp hq).2
  have dr : r∈g.coreShared.image g.point := by rw [ge]; exact (mem_inter.mp hr).2
  have cb := chart_three_boundary G f df p q r cp cq cr pq pr qr
  have db := chart_three_boundary G g dg p q r dp dq dr pq pr qr
  rw [fc] at cb
  rw [gd] at db
  have used (x y : Point) (h : {x,y}∈twoCoreEdges n L G) : {x,y}∈usedEdges G :=
    (mem_filter.mp (mem_sdiff.mp h).1).1
  have vc : c∈vertices n L := (mem_filter.mp hcC).1
  have vd : d∈vertices n L := (mem_filter.mp hdC).1
  have vp : p∈vertices n L := (mem_filter.mp (mem_filter.mp (mem_inter.mp hp).1).1).1
  have vq : q∈vertices n L := (mem_filter.mp (mem_filter.mp (mem_inter.mp hq).1).1).1
  have vr : r∈vertices n L := (mem_filter.mp (mem_filter.mp (mem_inter.mp hr).1).1).1
  exact certificate_boundary_pair_centers_unique n L hL hn tri ht p q r c d cb.1
    vp vq vr vc vd cb.2 db.2
    (used c p (mem_filter.mp (mem_inter.mp hp).1).2)
    (used c q (mem_filter.mp (mem_inter.mp hq).1).2)
    (used c r (mem_filter.mp (mem_inter.mp hr).1).2)
    (used d p (mem_filter.mp (mem_inter.mp hp).2).2)
    (used d q (mem_filter.mp (mem_inter.mp hq).2).2)
    (used d r (mem_filter.mp (mem_inter.mp hr).2).2)

theorem certificate_common_neighbor_card_le_two {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (c d : Point) (hc : AntipodalCore n L hL hn tri ht c)
    (hd : AntipodalCore n L hL hn tri ht d) (ne : c≠d) :
    (coreNeighbors n L (fun a => ofPredicate n L (tri a) hL (ht a)) c∩
      coreNeighbors n L (fun a => ofPredicate n L (tri a) hL (ht a)) d).card≤2 := by
  classical
  by_contra h
  obtain ⟨p,q,r,hp,hq,hr,pq,pr,qr⟩ := two_lt_card_iff.mp (lt_of_not_ge h)
  exact ne (certificate_three_common_neighbors_unique n L hL hn tri hi ht c d hc hd
    p q r hp hq hr pq pr qr)

#print axioms certificate_common_neighbor_card_le_two
end Kobon.UpperOpenMathAntipodalThreeNeighbors
