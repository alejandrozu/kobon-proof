import Kobon.UpperOpenMathPaidZeroTypes

/-! All full zero-paid types join the maximum-norm escape cluster. -/
namespace Kobon.UpperOpenMathPaidZeroEscape
open Cells FanGeometry UpperFan UpperVertexBudget UpperTriangleIncidence UpperSharedIncidence
  UpperCoreExtraction UpperOpenMathCapHeavyTriples UpperOpenMathCoreComponents
  UpperOpenMathActualFans UpperOpenMathRadialOrder UpperOpenMathMarkedPorts
  UpperOpenMathMarkedZeroGeometry UpperOpenMathAntipodalEscape UpperOpenMathPaidZeroTypes Finset
open scoped BigOperators
set_option maxHeartbeats 1000000

theorem closed_paid_zero_escape {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (triples : ∀ p∈core n L, (supports n L p).card=3)
    (P : Finset Point) (sub : P⊆core n L) (nonempty : P.Nonempty)
    (closed : SharedCoreClosed n L (fun a => ofPredicate n L (tri a) hL (ht a)) P)
    (tight : TightOn n L hL hn tri ht P)
    (types : ∀ p∈P, ZeroType
      (ordinaryDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) p)
      (coreDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) p)
      (markedCount n L hL hn tri ht p))
    (noRigid : ∀ p∈P, ¬(ordinaryDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) p=2 ∧
      coreDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) p=2 ∧ markedCount n L hL hn tri ht p=0)) :
    False := by
  classical
  let G := fun a => ofPredicate n L (tri a) hL (ht a)
  let a := ordinaryDegree n L G
  let d := coreDegree n L G
  let m := markedCount n L hL hn tri ht
  let F := P.filter (fun p => a p+d p=6)
  have localTypes (p : Point) (hp : p∈P) : ZeroType (a p) (d p) (m p) := types p hp
  have markedF (p : Point) (hp : p∈P) (e : Edge) (he : e∈markedEdges n L hL hn tri ht p) : p∈F := by
    have positive : 0<m p := card_pos.mpr ⟨e,he⟩
    have typ := marked_positive_type (a p) (d p) (m p) (localTypes p hp) positive
    exact mem_filter.mpr ⟨hp,by omega⟩
  have unmarkedNeighborF (p q : Point) (hp : p∈P) (hq : q∈P)
      (edge : {p,q}∈twoCoreEdges n L G)
      (unmarked : {p,q}∉markedEdges n L hL hn tri ht p) : q∈F := by
    rcases localTypes q hq with r|h|b|f|v|o
    · exact False.elim (noRigid q hq r)
    · exact mem_filter.mpr ⟨hq,by omega⟩
    · have poor : a q≤1 ∧ a q+d q≤2 := by omega
      exact False.elim (unmarked_target_not_poor n L hL hn tri hi ht triples P sub closed tight
        p q hq poor edge unmarked)
    · exact mem_filter.mpr ⟨hq,by omega⟩
    · exact mem_filter.mpr ⟨hq,by omega⟩
    · exact mem_filter.mpr ⟨hq,by omega⟩
  have surrounding (p : Point) (hp : p∈P) (full : a p+d p=6) (zero : m p=0) : Surrounded F p := by
    intro w hw valid
    have rp := triples p (sub hp)
    have fullActual : ordinaryDegree n L G p+coreDegree n L G p=2*(supports n L p).card := by
      change a p+d p=2*(supports n L p).card
      rw [full,rp]
    obtain ⟨q,qcore,edge,neg⟩ := UpperOpenMathFullSharing.certificate_full_sharing_neighbors_surround
      n L hL hn tri hi ht p (sub hp) w hw valid fullActual
    have qp : q∈P := closed {p,q} edge p (by simp) hp (by simp)
    exact ⟨q,unmarkedNeighborF p q hp qp edge
      (no_marked_edge_of_zero n L hL hn tri ht p zero {p,q}),neg⟩
  have bridge (p : Point) (hp : p∈P) (cap : a p=2 ∧ d p=4 ∧ m p=1) : AntipodalBridge F p := by
    have rp := triples p (sub hp)
    letI : NeZero (2*(supports n L p).card) := ⟨by omega⟩
    let D := atPoint n L hL hn p
    let g := atCoreFan n L hL hn tri ht p (sub hp)
    have positive : 0<m p := by rw [cap.2.2]; decide
    obtain ⟨e,he⟩ := card_pos.mp positive
    obtain ⟨z,zc,prev,next,epair⟩ := marked_edge_ray n L hL hn tri ht p (sub hp) e he
    let b := g.point z
    have eb : {p,b}∈markedEdges n L hL hn tri ht p := by simpa only [epair] using he
    have spec := marked_edge_spec n L hL hn tri hi ht triples p (sub hp) {p,b} eb
    have bcore := fan_core_endpoint n L hL hn tri ht p (mem_filter.mp (sub hp)).1 D (by omega) hi (sub hp) z zc
    have bp : b∈P := closed {p,b} spec.1 p (by simp) hp (by simp)
    have bne : b≠p := fan_point_ne_center n L hL hn tri ht p (mem_filter.mp (sub hp)).1 D (by omega) z
    have poor := spec.2.2.2 b (by simp) bne
    have blo : a b≤1 ∧ a b+d b≤2 := (mem_filter.mp poor).2.2
    have btype : a b=0 ∧ d b=2 := by
      rcases localTypes b bp with r|h|bdata|f|v|o <;> omega
    obtain ⟨u,uc,bu,k,hk,uk⟩ := marked_poor_antipodal_neighbor
      n L hL hn tri hi ht triples p b (sub hp) bcore eb bne btype.1 btype.2
    obtain ⟨s,sp,sne,marked⟩ := tight_marked_edge_coverage n L hL hn tri hi ht triples P sub closed tight
      b (mem_filter.mpr ⟨bp,by change a b≤1 ∧ a b+d b≤2; omega⟩) {b,u} bu (by simp)
    have ms := marked_edge_spec n L hL hn tri hi ht triples s (sub sp) {b,u} marked
    have su : s=u := by
      rcases mem_insert.mp ms.2.1 with he|he
      · exact False.elim (sne he)
      · exact mem_singleton.mp he
    have uF : u∈F := by simpa only [su] using markedF s sp {b,u} marked
    have ga : g.ordinaryShared.card=2 := (at_core_ordinary_card n L hL hn tri hi ht p (sub hp)).trans cap.1
    have gd : g.coreShared.card=4 := (at_core_core_card n L hL hn tri hi ht p (sub hp)).trans cap.2.1
    obtain ⟨opp,np,nn⟩ := UpperOpenMathMarkedFanShapes.full_two_cap_opposite_card rp g ga gd z prev next
    let q := g.point (z+3)
    have pq := (fan_core_iff n L hL hn tri ht p (mem_filter.mp (sub hp)).1 D (by omega) hi (sub hp) (z+3)).mp opp
    have qp : q∈P := closed {p,q} pq p (by simp) hp (by simp)
    have prevIndex : (z+3)-1=z+2 := by ring
    have np' : ¬OrdinaryAt n L (g.point ((z+3)-1)) := by simpa only [prevIndex] using np
    have notMarked : {p,q}∉markedEdges n L hL hn tri ht p :=
      nonordinary_port_not_marked n L hL hn tri ht p (sub hp) (z+3) np'
    have qF := unmarkedNeighborF p q hp qp pq notMarked
    obtain ⟨t,ht,qt⟩ := g.antipodal z
    have index : z+((supports n L p).card : ZMod (2*(supports n L p).card))=z+3 :=
      congrArg (fun t : ℕ => z+(t : ZMod (2*(supports n L p).card))) rp
    rw [index] at qt
    exact ⟨b,u,q,uF,qF,Ne.symm bne,k,t,hk,ht,uk,qt⟩
  have fNonempty : F.Nonempty := by
    obtain ⟨p,hp⟩ := nonempty
    rcases localTypes p hp with r|h|b|f|v|o
    · exact False.elim (noRigid p hp r)
    · exact ⟨p,mem_filter.mpr ⟨hp,by omega⟩⟩
    · have dpos : 0<((twoCoreEdges n L G).filter (fun e => p∈e)).card := by
        change 0<d p
        omega
      obtain ⟨e,he⟩ := card_pos.mp dpos
      obtain ⟨he,hpe⟩ := mem_filter.mp he
      obtain ⟨s,hs,sne,marked⟩ := tight_marked_edge_coverage n L hL hn tri hi ht triples P sub closed tight
        p (mem_filter.mpr ⟨hp,by change a p≤1 ∧ a p+d p≤2; omega⟩) e he hpe
      exact ⟨s,markedF s hs e marked⟩
    · exact ⟨p,mem_filter.mpr ⟨hp,by omega⟩⟩
    · exact ⟨p,mem_filter.mpr ⟨hp,by omega⟩⟩
    · exact ⟨p,mem_filter.mpr ⟨hp,by omega⟩⟩
  apply finite_mixed_escape_impossible F fNonempty
  intro p hp
  obtain ⟨hpP,full⟩ := mem_filter.mp hp
  by_cases zero : m p=0
  · exact Or.inl (surrounding p hpP full zero)
  · have positive : 0<m p := by omega
    exact Or.inr (bridge p hpP (marked_positive_type (a p) (d p) (m p) (localTypes p hpP) positive))

#print axioms closed_paid_zero_escape
end Kobon.UpperOpenMathPaidZeroEscape
