import Kobon.UpperOpenMathMarkedZeroGeometry

/-! A closed zero-curvature cluster cannot close under marked continuations. -/
namespace Kobon.UpperOpenMathMarkedZeroEscape
open Cells FanGeometry UpperFan UpperVertexBudget UpperTriangleIncidence UpperSharedIncidence
  UpperCoreExtraction UpperOpenMathCapHeavyTriples UpperOpenMathCoreComponents
  UpperOpenMathActualFans UpperOpenMathRadialOrder UpperOpenMathMarkedPorts
  UpperOpenMathTripleCharts UpperOpenMathAntipodalEscape UpperOpenMathMarkedZeroGeometry Finset
open scoped BigOperators

theorem closed_marked_zero_impossible {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (triples : ∀ p∈core n L, (supports n L p).card=3)
    (P : Finset Point) (sub : P⊆core n L) (nonempty : P.Nonempty)
    (closed : SharedCoreClosed n L (fun a => ofPredicate n L (tri a) hL (ht a)) P)
    (tight : (∑ p∈P, markedCount n L hL hn tri ht p)=
      ∑ p∈P.filter (fun p => ordinaryDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) p≤1 ∧
        ordinaryDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) p+
          coreDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) p≤2),
        coreDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) p)
    (types : ∀ p∈P,
      (ordinaryDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) p=2 ∧
        coreDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) p=2 ∧ markedCount n L hL hn tri ht p=0) ∨
      (ordinaryDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) p=2 ∧
        coreDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) p=4 ∧ markedCount n L hL hn tri ht p=1) ∨
      (ordinaryDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) p=0 ∧
        coreDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) p=2 ∧ markedCount n L hL hn tri ht p=0) ∨
      (ordinaryDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) p=0 ∧
        coreDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) p=6 ∧ markedCount n L hL hn tri ht p=0)) : False := by
  classical
  let G := fun a => ofPredicate n L (tri a) hL (ht a)
  let a := ordinaryDegree n L G
  let d := coreDegree n L G
  let m := markedCount n L hL hn tri ht
  let F := P.filter (fun p => (a p=2 ∧ d p=4 ∧ m p=1) ∨ (a p=0 ∧ d p=6 ∧ m p=0))
  have markedSourceF (s : Point) (hs : s∈P) (e : Edge) (he : e∈markedEdges n L hL hn tri ht s) : s∈F := by
    have positive : 0<m s := card_pos.mpr ⟨e,he⟩
    rcases types s hs with r|h|b|f
    · change a s=2 ∧ d s=2 ∧ m s=0 at r
      omega
    · exact mem_filter.mpr ⟨hs,Or.inl h⟩
    · change a s=0 ∧ d s=2 ∧ m s=0 at b
      omega
    · change a s=0 ∧ d s=6 ∧ m s=0 at f
      omega
  have noMarked (p : Point) (zero : m p=0) (e : Edge) : e∉markedEdges n L hL hn tri ht p := by
    intro he
    have pos : 0<m p := card_pos.mpr ⟨e,he⟩
    omega
  have fullInF (p : Point) (hp : p∈P) (full : a p=0 ∧ d p=6 ∧ m p=0) : Surrounded F p := by
    intro w hw valid
    have rp := triples p (sub hp)
    have fullDegree : coreDegree n L G p=2*(supports n L p).card := by
      change d p=2*(supports n L p).card
      rw [full.2.1,rp]
    obtain ⟨q,hq,e,neg⟩ := UpperOpenMathFullCoreFans.certificate_full_core_neighbors_surround
      n L hL hn tri hi ht p (sub hp) w hw valid fullDegree
    have hqP : q∈P := closed {p,q} e p (by simp) hp (by simp)
    have qF : q∈F := by
      rcases types q hqP with r|h|b|f
      · obtain ⟨nf,nc,df⟩ := certificate_normalized_two_two_of_zero_marks
          n L hL hn tri hi ht q hq (triples q hq) r.1 r.2.1 r.2.2
        have ne : {nf.center,p}∈twoCoreEdges n L G := by simpa only [nc,pair_comm] using e
        exact False.elim (UpperOpenMathTripleZeroCurvature.certificate_normalized_full_not_adjacent
          n L hL hn tri hi ht nf df p (sub hp) fullDegree ne)
      · exact mem_filter.mpr ⟨hqP,Or.inl h⟩
      · have poor : a q≤1 ∧ a q+d q≤2 := by change a q=0 ∧ d q=2 ∧ m q=0 at b; omega
        exact False.elim (unmarked_target_not_poor n L hL hn tri hi ht triples P sub closed tight
          p q hqP poor e (noMarked p full.2.2 {p,q}))
      · exact mem_filter.mpr ⟨hqP,Or.inr f⟩
    exact ⟨q,qF,neg⟩
  have markedInF (p : Point) (hp : p∈P) (cap : a p=2 ∧ d p=4 ∧ m p=1) : AntipodalBridge F p := by
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
    have blo := (mem_filter.mp poor).2.2
    have btype : a b=0 ∧ d b=2 := by
      have hlow : a b≤1 ∧ a b+d b≤2 := blo
      rcases types b bp with r|h|bdata|f
      · change a b=2 ∧ d b=2 ∧ m b=0 at r
        omega
      · change a b=2 ∧ d b=4 ∧ m b=1 at h
        omega
      · change a b=0 ∧ d b=2 ∧ m b=0 at bdata
        exact ⟨bdata.1,bdata.2.1⟩
      · change a b=0 ∧ d b=6 ∧ m b=0 at f
        omega
    obtain ⟨u,uc,bu,k,hk,uk⟩ := marked_poor_antipodal_neighbor
      n L hL hn tri hi ht triples p b (sub hp) bcore eb bne btype.1 btype.2
    obtain ⟨s,sp,sne,marked⟩ := tight_marked_edge_coverage n L hL hn tri hi ht triples P sub closed tight
      b (mem_filter.mpr ⟨bp,by change a b≤1 ∧ a b+d b≤2; omega⟩) {b,u} bu (by simp)
    have ms := marked_edge_spec n L hL hn tri hi ht triples s (sub sp) {b,u} marked
    have su : s=u := by
      rcases mem_insert.mp ms.2.1 with he|he
      · exact False.elim (sne he)
      · exact mem_singleton.mp he
    have uF : u∈F := by simpa only [su] using markedSourceF s sp {b,u} marked
    have ga : g.ordinaryShared.card=2 := (at_core_ordinary_card n L hL hn tri hi ht p (sub hp)).trans cap.1
    have gd : g.coreShared.card=4 := (at_core_core_card n L hL hn tri hi ht p (sub hp)).trans cap.2.1
    obtain ⟨opp,np,nn⟩ := UpperOpenMathMarkedFanShapes.full_two_cap_opposite_card rp g ga gd z prev next
    let q := g.point (z+3)
    have qc := fan_core_endpoint n L hL hn tri ht p (mem_filter.mp (sub hp)).1 D (by omega) hi (sub hp) (z+3) opp
    have pq := (fan_core_iff n L hL hn tri ht p (mem_filter.mp (sub hp)).1 D (by omega) hi (sub hp) (z+3)).mp opp
    have qP : q∈P := closed {p,q} pq p (by simp) hp (by simp)
    have prevIndex : (z+3)-1=z+2 := by ring
    have nextIndex : (z+3)+1=z+4 := by ring
    have np' : ¬OrdinaryAt n L (g.point ((z+3)-1)) := by simpa only [prevIndex] using np
    have nn' : ¬OrdinaryAt n L (g.point ((z+3)+1)) := by simpa only [nextIndex] using nn
    have notMarked : {p,q}∉markedEdges n L hL hn tri ht p :=
      nonordinary_port_not_marked n L hL hn tri ht p (sub hp) (z+3) np'
    have qF : q∈F := by
      rcases types q qP with r|h|b|f
      · obtain ⟨nf,nc,df⟩ := certificate_normalized_two_two_of_zero_marks
          n L hL hn tri hi ht q qc (triples q qc) r.1 r.2.1 r.2.2
        exact False.elim (normalized_nonordinary_port_not_adjacent n L hL hn tri hi ht nf df p (sub hp)
          (z+3) opp (by rw [nc]) np' nn')
      · exact mem_filter.mpr ⟨qP,Or.inl h⟩
      · have plow : a q≤1 ∧ a q+d q≤2 := by change a q=0 ∧ d q=2 ∧ m q=0 at b; omega
        exact False.elim (unmarked_target_not_poor n L hL hn tri hi ht triples P sub closed tight p q qP plow pq notMarked)
      · exact mem_filter.mpr ⟨qP,Or.inr f⟩
    obtain ⟨t,ht,qt⟩ := g.antipodal z
    have index : z+((supports n L p).card : ZMod (2*(supports n L p).card))=z+3 :=
      congrArg (fun t : ℕ => z+(t : ZMod (2*(supports n L p).card))) rp
    rw [index] at qt
    exact ⟨b,u,q,uF,qF,Ne.symm bne,k,t,hk,ht,uk,qt⟩
  by_cases fNonempty : F.Nonempty
  · apply finite_mixed_escape_impossible F fNonempty
    intro p hp
    obtain ⟨hpP,hpType⟩ := mem_filter.mp hp
    rcases hpType with marked|full
    · exact Or.inr (markedInF p hpP marked)
    · exact Or.inl (fullInF p hpP full)
  · have fEmpty : F=∅ := not_nonempty_iff_eq_empty.mp fNonempty
    have rigid (p : Point) (hp : p∈P) : (supports n L p).card=3 ∧ a p=2 ∧ d p=2 := by
      have rp := triples p (sub hp)
      rcases types p hp with r|h|b|f
      · exact ⟨rp,r.1,r.2.1⟩
      · have hm : p∈F := mem_filter.mpr ⟨hp,Or.inl h⟩
        rw [fEmpty] at hm
        exact False.elim (notMem_empty p hm)
      · have dpos : 0<((twoCoreEdges n L G).filter (fun e => p∈e)).card := by
          change a p=0 ∧ d p=2 ∧ m p=0 at b
          change 0<d p
          rw [b.2.1]
          decide
        obtain ⟨e,he⟩ := card_pos.mp dpos
        obtain ⟨heD,hep⟩ := mem_filter.mp he
        obtain ⟨s,hs,sne,marked⟩ := tight_marked_edge_coverage n L hL hn tri hi ht triples P sub closed tight
          p (mem_filter.mpr ⟨hp,by
            change a p=0 ∧ d p=2 ∧ m p=0 at b
            change a p≤1 ∧ a p+d p≤2
            omega⟩) e heD hep
        have sm := markedSourceF s hs e marked
        rw [fEmpty] at sm
        exact False.elim (notMem_empty s sm)
      · have hm : p∈F := mem_filter.mpr ⟨hp,Or.inr f⟩
        rw [fEmpty] at hm
        exact False.elim (notMem_empty p hm)
    exact UpperOpenMathTwoTwoCore.certificate_closed_two_two_impossible
      n L hL hn tri hi ht P sub nonempty closed rigid

#print axioms closed_marked_zero_impossible
end Kobon.UpperOpenMathMarkedZeroEscape
