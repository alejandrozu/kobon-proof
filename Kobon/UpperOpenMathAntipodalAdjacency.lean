import Kobon.UpperOpenMathAntipodalStarDegree
import Kobon.UpperOpenMathFiberMatching

/-!
Two unmarked full two-cap triple fans cannot share a core side.
The local proof uses actual fan supports and the third indexed support at
the shared outer triple vertex. The forbidden continuation would make the
opposite old star diagonal an actual used edge. Marked two-cap neighbors
are deliberately outside this statement.
-/
namespace Kobon.UpperOpenMathAntipodalAdjacency
open Cells FanGeometry UpperFan UpperVertexBudget UpperTriangleIncidence
  UpperSharedIncidence UpperCoreExtraction UpperOpenMathAntipodalTwoCapChart
  UpperOpenMathAntipodalStarDegree UpperOpenMathSectorRecords Finset
open scoped BigOperators

set_option maxHeartbeats 1000000

@[simp] theorem cyclic_three_sub_one : (3 : ZMod 6)-1=2 := by decide
@[simp] theorem cyclic_zero_sub_one : (0 : ZMod 6)-1=5 := by decide
@[simp] theorem cyclic_neg_one : (-1 : ZMod 6)=5 := by decide
@[simp] theorem cyclic_three_add_one : (3 : ZMod 6)+1=4 := by decide
@[simp] theorem cyclic_one_add_three : (1 : ZMod 6)+3=4 := by decide
@[simp] theorem cyclic_two_add_three : (2 : ZMod 6)+3=5 := by decide
@[simp] theorem cyclic_three_add_two : (3 : ZMod 6)+2=5 := by decide
@[simp] theorem cyclic_three_add_three : (3 : ZMod 6)+3=0 := by decide
@[simp] theorem cyclic_two_sub_one : (2 : ZMod 6)-1=1 := by decide
@[simp] theorem cyclic_five_sub_one : (5 : ZMod 6)-1=4 := by decide
@[simp] theorem cyclic_five_add_one : (5 : ZMod 6)+1=0 := by decide
@[simp] theorem cyclic_one_add_one : (1 : ZMod 6)+1=2 := by decide
@[simp] theorem cyclic_two_add_one : (2 : ZMod 6)+1=3 := by decide

theorem det_ne_of_distinct (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L)
    (i j : Fin n) (h : i≠j) : det (L i) (L j)≠0 := by
  rcases lt_or_gt_of_ne h with hi|hi
  · exact hL i j hi
  · have hp := hL j i hi
    have he : det (L i) (L j)= -det (L j) (L i) := by dsimp [det]; ring
    rw [he]
    exact neg_ne_zero.mpr hp

theorem support_eq_of_two_points (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L)
    (i j : Fin n) (p q : Point) (hne : p≠q)
    (hip : affineEval (L i) p=0) (hiq : affineEval (L i) q=0)
    (hjp : affineEval (L j) p=0) (hjq : affineEval (L j) q=0) : i=j := by
  by_contra h
  exact hne (two_lines_two_points (L i) (L j) p q
    (det_ne_of_distinct n L hL i j h) hip hiq hjp hjq)

theorem cap_left {n : ℕ} {L : ℕ → Line ℝ} (f : Sectors n 3 L)
    (hall : f.triangular=univ) (z : ZMod 6) :
    affineEval (L (f.opposite z)) (f.point z)=0 := by
  have hz : z∈f.triangular := by rw [hall]; simp
  simpa only [f.triangle_support z hz,f.triangle_left z hz] using (f.triangle z).Aq

theorem cap_right {n : ℕ} {L : ℕ → Line ℝ} (f : Sectors n 3 L)
    (hall : f.triangular=univ) (z : ZMod 6) :
    affineEval (L (f.opposite z)) (f.point (z+1))=0 := by
  have hz : z∈f.triangular := by rw [hall]; simp
  simpa only [f.triangle_support z hz,f.triangle_right z hz] using (f.triangle z).Ar

theorem cap_avoids {n : ℕ} {L : ℕ → Line ℝ} (f : Sectors n 3 L)
    (hall : f.triangular=univ) (z : ZMod 6) :
    affineEval (L (f.opposite z)) f.center≠0 := by
  have hz : z∈f.triangular := by rw [hall]; simp
  simpa only [f.triangle_support z hz,f.triangle_center z hz] using (f.triangle z).Ap

theorem cap_eq_at_ordinary {n : ℕ} {L : ℕ → Line ℝ} (f : Sectors n 3 L)
    (hall : f.triangular=univ) (z : ZMod 6) (ho : OrdinaryAt n L (f.point z)) :
    f.opposite (z-1)=f.opposite z := by
  apply ordinary_nonradial_unique n L (f.point z) ho (f.radial z)
    (f.opposite (z-1)) (f.opposite z) (f.radial_point z)
  · simpa only [sub_add_cancel] using cap_right f hall (z-1)
  · exact cap_left f hall z
  · intro h
    exact cap_avoids f hall (z-1) (by rw [h]; exact f.radial_center z)
  · intro h
    exact cap_avoids f hall z (by rw [h]; exact f.radial_center z)

theorem antipodal_line_point {n : ℕ} {L : ℕ → Line ℝ} (f : Sectors n 3 L)
    (w : Line ℝ) (z : ZMod 6) (hc : affineEval w f.center=0)
    (hp : affineEval w (f.point z)=0) : affineEval w (f.point (z+3))=0 := by
  obtain ⟨s,hs,he⟩ := f.antipodal z
  simp only [Nat.cast_ofNat] at he
  rw [he]
  have hid : affineEval w
      (f.center.1-s*((f.point z).1-f.center.1),
       f.center.2-s*((f.point z).2-f.center.2))=
      (1+s)*affineEval w f.center-s*affineEval w (f.point z) := by
    dsimp [affineEval]; ring
  rw [hid,hc,hp]
  ring

theorem antipodal_line_center {n : ℕ} {L : ℕ → Line ℝ} (f : Sectors n 3 L)
    (w : Line ℝ) (z : ZMod 6) (hp : affineEval w (f.point z)=0)
    (hq : affineEval w (f.point (z+3))=0) : affineEval w f.center=0 := by
  obtain ⟨s,hs,he⟩ := f.antipodal z
  simp only [Nat.cast_ofNat] at he
  rw [he] at hq
  have hid : affineEval w
      (f.center.1-s*((f.point z).1-f.center.1),
       f.center.2-s*((f.point z).2-f.center.2))=
      (1+s)*affineEval w f.center-s*affineEval w (f.point z) := by
    dsimp [affineEval]; ring
  rw [hid,hp,mul_zero,sub_zero] at hq
  exact (mul_eq_zero.mp hq).resolve_left (by linarith)

theorem mem_three_of_card_three {β : Type*} [DecidableEq β]
    (S : Finset β) (a b c d : β) (hs : S.card=3)
    (hab : a≠b) (hac : a≠c) (hbc : b≠c)
    (ha : a∈S) (hb : b∈S) (hc : c∈S) (hd : d∈S) : d=a∨d=b∨d=c := by
  have sub : ({a,b,c} : Finset β)⊆S := by
    intro x hx
    rcases (by simpa only [mem_insert,mem_singleton] using hx : x=a∨x=b∨x=c) with rfl|rfl|rfl
    all_goals assumption
  have he : ({a,b,c} : Finset β)=S := by
    apply eq_of_subset_of_card_le sub
    simpa [hs,hab,hac,hbc]
  rw [←he] at hd
  simpa only [mem_insert,mem_singleton] using hd

/-- The local matched charts force a blocked old diagonal to become used. -/
theorem normalized_pair_incompatible {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L)
    (tri : α → Triple) (ht : ∀ a, TrianglePredicate n L (tri a))
    (f g : Sectors n 3 L)
    (df : AntipodalData (fun a => ofPredicate n L (tri a) hL (ht a)) f)
    (dg : AntipodalData (fun a => ofPredicate n L (tri a) hL (ht a)) g)
    (center : g.center=f.point 1) (back : g.point 2=f.center)
    (right : g.point 1=f.point 2) (left : g.point 3=f.point 0)
    (triple : (supports n L (f.point 2)).card=3) : False := by
  classical
  let G := fun a => ofPredicate n L (tri a) hL (ht a)
  have fo0 : OrdinaryAt n L (f.point 0) :=
    ((f.mem_ordinaryShared 0).mp (by rw [df.ordinary_eq]; simp)).2.2
  have fo3 : OrdinaryAt n L (f.point 3) :=
    ((f.mem_ordinaryShared 3).mp (by rw [df.ordinary_eq]; simp)).2.2
  have go0 : OrdinaryAt n L (g.point 0) :=
    ((g.mem_ordinaryShared 0).mp (by rw [dg.ordinary_eq]; simp)).2.2
  have go3 : OrdinaryAt n L (g.point 3) :=
    ((g.mem_ordinaryShared 3).mp (by rw [dg.ordinary_eq]; simp)).2.2
  have feq23 : f.opposite 2=f.opposite 3 := by
    simpa using cap_eq_at_ordinary f df.triangular_eq 3 fo3
  have geq50 : g.opposite 5=g.opposite 0 := by
    simpa using cap_eq_at_ordinary g dg.triangular_eq 0 go0
  have gh5 : affineEval (L (g.opposite 0)) (g.point 5)=0 := by
    rw [←geq50]
    exact cap_left g dg.triangular_eq 5
  have fh4 : affineEval (L (f.opposite 2)) (f.point 4)=0 := by
    rw [feq23]
    simpa using cap_right f df.triangular_eq 3
  have f14 : affineEval (L (f.radial 1)) (f.point 4)=0 := by
    simpa using antipodal_line_point f (L (f.radial 1)) 1
      (f.radial_center 1) (f.radial_point 1)
  have ge1 : g.radial 1=f.opposite 1 := by
    apply support_eq_of_two_points n L hL _ _ g.center (g.point 1)
      (dg.noncentral 1).symm
    · exact g.radial_center 1
    · exact g.radial_point 1
    · rw [center]; exact cap_left f df.triangular_eq 1
    · rw [right]; simpa using cap_right f df.triangular_eq 1
  have ge2 : g.radial 2=f.radial 1 := by
    apply support_eq_of_two_points n L hL _ _ g.center (g.point 2)
      (dg.noncentral 2).symm
    · exact g.radial_center 2
    · exact g.radial_point 2
    · rw [center]; exact f.radial_point 1
    · rw [back]; exact f.radial_center 1
  have gcap1 : g.opposite 1=f.radial 2 := by
    apply support_eq_of_two_points n L hL _ _ (g.point 1) (g.point 2)
      (fun he=>(by decide : (1 : ZMod 6)≠2) (dg.injective he))
    · exact cap_left g dg.triangular_eq 1
    · simpa using cap_right g dg.triangular_eq 1
    · rw [right]; exact f.radial_point 2
    · rw [back]; exact f.radial_center 2
  have f12ne : f.radial 2≠f.opposite 1 := by
    intro he
    exact cap_avoids f df.triangular_eq 1 (by rw [←he]; exact f.radial_center 2)
  have f22ne : f.radial 2≠f.opposite 2 := by
    intro he
    exact cap_avoids f df.triangular_eq 2 (by rw [←he]; exact f.radial_center 2)
  have fcap_nonzero : affineEval (L (f.opposite 2)) (f.point 1)≠0 := by
    intro hp
    exact cap_avoids f df.triangular_eq 2
      (antipodal_line_center f (L (f.opposite 2)) 1 hp (by simpa using fh4))
  have fop_ne : f.opposite 1≠f.opposite 2 := by
    intro he
    exact fcap_nonzero (by rw [←he]; exact cap_left f df.triangular_eq 1)
  have gmA : affineEval (L (g.opposite 0)) (f.point 2)=0 := by
    rw [←right]
    simpa using cap_right g dg.triangular_eq 0
  have gmB : g.opposite 0≠f.opposite 1 := by
    intro he
    exact cap_avoids g dg.triangular_eq 0 (by rw [he,center]; exact cap_left f df.triangular_eq 1)
  have gmC : g.opposite 0≠f.radial 2 := by
    intro he
    have hc : affineEval (L (g.opposite 0)) (g.point 2)=0 := by
      rw [he,back]; exact f.radial_center 2
    exact cap_avoids g dg.triangular_eq 0
      (antipodal_line_center g (L (g.opposite 0)) 2 hc (by simpa using gh5))
  have member (a : Fin n) (ha : affineEval (L a) (f.point 2)=0) :
      a∈supports n L (f.point 2) := by simp [supports,ha]
  have cases := mem_three_of_card_three (supports n L (f.point 2))
    (f.radial 2) (f.opposite 1) (f.opposite 2) (g.opposite 0) triple
    f12ne f22ne fop_ne (member _ (f.radial_point 2))
    (member _ (by simpa using cap_right f df.triangular_eq 1))
    (member _ (cap_left f df.triangular_eq 2)) (member _ gmA)
  have gcap0 : g.opposite 0=f.opposite 2 := cases.resolve_left gmC |>.resolve_left gmB
  have ghline : affineEval (L (f.radial 1)) (g.point 5)=0 := by
    rw [←ge2]
    simpa using antipodal_line_point g (L (g.radial 2)) 2
      (g.radial_center 2) (g.radial_point 2)
  have ghcap : affineEval (L (f.opposite 2)) (g.point 5)=0 := by rw [←gcap0]; exact gh5
  have hradne : f.radial 1≠f.opposite 2 := by
    intro he
    exact cap_avoids f df.triangular_eq 2 (by rw [←he]; exact f.radial_center 1)
  have point5 : g.point 5=f.point 4 := two_lines_two_points _ _ _ _
    (det_ne_of_distinct n L hL _ _ hradne) ghline f14 ghcap fh4
  obtain ⟨block,_,_,_⟩ := certificate_star_blocks n L hL tri ht f df
  have used := occurrence_radial_used G g dg.toFullData 5
  exact block (by simpa only [center,point5] using used)

theorem charts_neighbor_matching {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (f g : Sectors n 3 L)
    (df : AntipodalData (fun a => ofPredicate n L (tri a) hL (ht a)) f)
    (dg : AntipodalData (fun a => ofPredicate n L (tri a) hL (ht a)) g)
    (z : ZMod 6) (hz : z∈f.coreShared) (center : g.center=f.point z) :
    ∃ w : ZMod 6, w∈g.coreShared ∧ g.point w=f.center ∧
      g.point (w-1)=f.point (z+1) ∧ g.point (w+1)=f.point (z-1) := by
  classical
  let G := fun a => ofPredicate n L (tri a) hL (ht a)
  have he : {g.center,f.center}∈twoCoreEdges n L G := by
    simpa only [center,pair_comm] using core_edge_of_label G f df.toFullData z hz
  have hm : ({g.center,f.center} : Edge)∈g.coreShared.image
      (fun w => ({g.center,g.point w} : Edge)) := by
    rw [dg.core_image]
    exact mem_filter.mpr ⟨he,by simp⟩
  obtain ⟨w,hw,hpair⟩ := mem_image.mp hm
  have hc : g.point w=f.center := by
    have hm : f.center∈({g.center,g.point w} : Edge) := by rw [hpair]; simp
    simp only [mem_insert,mem_singleton] at hm
    rcases hm with h|h
    · exact False.elim (df.noncentral z (center.symm.trans h.symm))
    · exact h.symm
  obtain ⟨o⟩ := df.occurrences (z-1) (by rw [df.triangular_eq]; simp)
  obtain ⟨p⟩ := df.occurrences z (by rw [df.triangular_eq]; simp)
  obtain ⟨a⟩ := dg.occurrences (w-1) (by rw [dg.triangular_eq]; simp)
  obtain ⟨b⟩ := dg.occurrences w (by rw [dg.triangular_eq]; simp)
  have disjoint : Pairwise (fun a b => Disjoint (G a).interior (G b).interior) := by
    intro a b hab
    exact distinct_interiors_disjoint n L _ _ hL (ht a) (ht b) (fun h=>hab (hi h))
  have hmatch := UpperOpenMathFiberMatching.neighboring_points_match G disjoint
    (by decide : 2≤3) (by decide : 2≤3) f.center g.center f.point g.point
    df.injective dg.injective df.noncentral dg.noncentral df.positive dg.positive
    z w center hc o p a b
  exact ⟨w,hw,hc,hmatch⟩

theorem first_ray_incompatible {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (f g : Sectors n 3 L)
    (df : AntipodalData (fun a => ofPredicate n L (tri a) hL (ht a)) f)
    (dg : AntipodalData (fun a => ofPredicate n L (tri a) hL (ht a)) g)
    (alltriple : ∀ c∈core n L, (supports n L c).card=3)
    (center : g.center=f.point 1) : False := by
  classical
  let G := fun a => ofPredicate n L (tri a) hL (ht a)
  have hcore1 : (1 : ZMod 6)∈f.coreShared := by rw [df.core_eq]; simp
  obtain ⟨w,hw,hback,hr,hl⟩ := charts_neighbor_matching n L hL tri hi ht f g df dg 1 hcore1 center
  have ordinary : OrdinaryAt n L (g.point (w+1)) := by
    rw [hl]
    simpa using ((f.mem_ordinaryShared 0).mp (by rw [df.ordinary_eq]; simp)).2.2
  have hord : w+1∈g.ordinaryShared := by
    rw [g.mem_ordinaryShared]
    exact ⟨by rw [dg.triangular_eq]; simp,by rw [dg.triangular_eq]; simp,ordinary⟩
  have hwcase : w=2∨w=5 := by
    have hh : w+1=0∨w+1=3 := by simpa only [dg.ordinary_eq,mem_insert,mem_singleton] using hord
    exact (by decide : ∀ w : ZMod 6, w+1=0∨w+1=3 → w=2∨w=5) w hh
  have triple : (supports n L (f.point 2)).card=3 := alltriple _
    (df.core_endpoint 2 (by rw [df.core_eq]; simp))
  rcases hwcase with rfl|rfl
  · exact normalized_pair_incompatible n L hL tri ht f g df dg center hback
      (by simpa using hr) (by simpa using hl) triple
  · let g' := UpperOpenMathRotation.Sectors.shift g 3
    have dg' := shift_three_data G g dg
    apply normalized_pair_incompatible n L hL tri ht f g' df dg'
    · exact center
    · simpa [g'] using hback
    · simpa [g'] using hr
    · simpa [g'] using hl
    · exact triple

theorem next_ordinary_reverse_incompatible {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (f g : Sectors n 3 L)
    (df : AntipodalData (fun a => ofPredicate n L (tri a) hL (ht a)) f)
    (dg : AntipodalData (fun a => ofPredicate n L (tri a) hL (ht a)) g)
    (alltriple : ∀ c∈core n L, (supports n L c).card=3)
    (z : ZMod 6) (hz : z∈f.coreShared) (next : z+1∈f.ordinaryShared)
    (center : g.center=f.point z) : False := by
  classical
  let G := fun a => ofPredicate n L (tri a) hL (ht a)
  obtain ⟨w,hw,hback,hr,hl⟩ := charts_neighbor_matching n L hL tri hi ht f g df dg z hz center
  have ordinary : OrdinaryAt n L (g.point (w-1)) := by
    rw [hr]
    exact ((f.mem_ordinaryShared (z+1)).mp next).2.2
  have hord : w-1∈g.ordinaryShared := by
    rw [g.mem_ordinaryShared]
    exact ⟨by rw [dg.triangular_eq]; simp,by rw [dg.triangular_eq]; simp,ordinary⟩
  have hwcase : w=1∨w=4 := by
    have hh : w-1=0∨w-1=3 := by simpa only [dg.ordinary_eq,mem_insert,mem_singleton] using hord
    exact (by decide : ∀ w : ZMod 6, w-1=0∨w-1=3 → w=1∨w=4) w hh
  rcases hwcase with rfl|rfl
  · exact first_ray_incompatible n L hL tri hi ht g f dg df alltriple hback.symm
  · let g' := UpperOpenMathRotation.Sectors.shift g 3
    have dg' := shift_three_data G g dg
    apply first_ray_incompatible n L hL tri hi ht g' f dg' df alltriple
    simpa [g'] using hback.symm

theorem charts_not_adjacent {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (f g : Sectors n 3 L)
    (df : AntipodalData (fun a => ofPredicate n L (tri a) hL (ht a)) f)
    (dg : AntipodalData (fun a => ofPredicate n L (tri a) hL (ht a)) g)
    (alltriple : ∀ c∈core n L, (supports n L c).card=3)
    (z : ZMod 6) (hz : z∈f.coreShared) (center : g.center=f.point z) : False := by
  classical
  let G := fun a => ofPredicate n L (tri a) hL (ht a)
  have hcase : z=1∨z=2∨z=4∨z=5 := by simpa only [df.core_eq,mem_insert,mem_singleton] using hz
  rcases hcase with rfl|rfl|rfl|rfl
  · exact first_ray_incompatible n L hL tri hi ht f g df dg alltriple center
  · apply next_ordinary_reverse_incompatible n L hL tri hi ht f g df dg alltriple 2 hz _ center
    rw [df.ordinary_eq]
    norm_num
  · let f' := UpperOpenMathRotation.Sectors.shift f 3
    have df' := shift_three_data G f df
    apply first_ray_incompatible n L hL tri hi ht f' g df' dg alltriple
    simpa [f'] using center
  · apply next_ordinary_reverse_incompatible n L hL tri hi ht f g df dg alltriple 5 hz _ center
    rw [df.ordinary_eq]
    simp

#print axioms normalized_pair_incompatible
#print axioms charts_neighbor_matching
#print axioms charts_not_adjacent

/-- Actual all-triple arrangements exclude an edge between two unmarked
full two-cap cores. No local chart or matching equation is assumed. -/
theorem certificate_unmarked_full_not_adjacent {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (alltriple : ∀ c∈core n L, (supports n L c).card=3)
    (c d : Point) (hc : c∈core n L) (hd : d∈core n L)
    (ac : UpperOpenMathCapHeavyTriples.ordinaryDegree n L
      (fun a => ofPredicate n L (tri a) hL (ht a)) c=2)
    (ad : UpperOpenMathCapHeavyTriples.ordinaryDegree n L
      (fun a => ofPredicate n L (tri a) hL (ht a)) d=2)
    (dc : UpperOpenMathCapHeavyTriples.coreDegree n L
      (fun a => ofPredicate n L (tri a) hL (ht a)) c=4)
    (dd : UpperOpenMathCapHeavyTriples.coreDegree n L
      (fun a => ofPredicate n L (tri a) hL (ht a)) d=4)
    (zc : UpperOpenMathMarkedPorts.markedCount n L hL hn tri ht c=0)
    (zd : UpperOpenMathMarkedPorts.markedCount n L hL hn tri ht d=0)
    (edge : {c,d}∈twoCoreEdges n L (fun a => ofPredicate n L (tri a) hL (ht a))) : False := by
  classical
  let G := fun a => ofPredicate n L (tri a) hL (ht a)
  obtain ⟨f,hfc,df⟩ := certificate_antipodal_chart n L hL hn tri hi ht c hc
    (alltriple c hc) ac dc zc
  obtain ⟨g,hgd,dg⟩ := certificate_antipodal_chart n L hL hn tri hi ht d hd
    (alltriple d hd) ad dd zd
  have used := (mem_filter.mp (mem_sdiff.mp edge).1).1
  have neq : d≠c := by
    intro he
    have hcard := used_edge_card G used
    simp [he] at hcard
  have he : ({f.center,g.center} : Edge)∈twoCoreEdges n L G := by
    simpa only [hfc,hgd] using edge
  have hm : ({f.center,g.center} : Edge)∈f.coreShared.image
      (fun z => ({f.center,f.point z} : Edge)) := by
    rw [df.core_image]
    exact mem_filter.mpr ⟨he,by simp⟩
  obtain ⟨z,hz,hpair⟩ := mem_image.mp hm
  have center : g.center=f.point z := by
    have hg : g.center∈({f.center,f.point z} : Edge) := by rw [hpair]; simp
    simp only [mem_insert,mem_singleton] at hg
    rcases hg with hg|hg
    · exact False.elim (neq (by simpa only [hfc,hgd] using hg))
    · exact hg
  exact charts_not_adjacent n L hL tri hi ht f g df dg alltriple z hz center

#print axioms certificate_unmarked_full_not_adjacent

noncomputable def unmarkedFullTwoCapSet {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (ht : ∀ a, TrianglePredicate n L (tri a)) : Finset Point := by
  classical
  let G := fun a => ofPredicate n L (tri a) hL (ht a)
  exact (core n L).filter fun c=>
    UpperOpenMathCapHeavyTriples.ordinaryDegree n L G c=2 ∧
    UpperOpenMathCapHeavyTriples.coreDegree n L G c=4 ∧
    UpperOpenMathMarkedPorts.markedCount n L hL hn tri ht c=0

theorem certificate_unmarked_incidence_bound {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (alltriple : ∀ c∈core n L, (supports n L c).card=3) :
    let G := fun a => ofPredicate n L (tri a) hL (ht a)
    (∑ c∈unmarkedFullTwoCapSet n L hL hn tri ht,
      UpperOpenMathCapHeavyTriples.coreDegree n L G c)≤(twoCoreEdges n L G).card := by
  classical
  let G := fun a => ofPredicate n L (tri a) hL (ht a)
  let X := unmarkedFullTwoCapSet n L hL hn tri ht
  have independent (e : Edge) (he : e∈twoCoreEdges n L G)
      (p : Point) (hp : p∈e∩X) (q : Point) (hq : q∈e∩X) : p=q := by
    by_contra hneq
    have hpE := (mem_inter.mp hp).1
    have hqE := (mem_inter.mp hq).1
    have hpX := mem_filter.mp (mem_inter.mp hp).2
    have hqX := mem_filter.mp (mem_inter.mp hq).2
    have used := (mem_filter.mp (mem_sdiff.mp he).1).1
    have hpair : ({p,q} : Edge)=e := by
      apply eq_of_subset_of_card_le
      · intro a ha
        rcases (by simpa only [mem_insert,mem_singleton] using ha : a=p∨a=q) with rfl|rfl
        all_goals assumption
      · rw [card_pair hneq,used_edge_card G used]
    exact certificate_unmarked_full_not_adjacent n L hL hn tri hi ht alltriple
      p q hpX.1 hqX.1 hpX.2.1 hqX.2.1 hpX.2.2.1 hqX.2.2.1
      hpX.2.2.2 hqX.2.2.2 (by simpa only [hpair] using he)
  exact UpperOpenMathTripleGraph.independent_incidence_bound (twoCoreEdges n L G) X independent

/-- Every unmarked full two-cap core uses four separately charged core edges. -/
theorem certificate_four_times_unmarked_card {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (alltriple : ∀ c∈core n L, (supports n L c).card=3) :
    4*(unmarkedFullTwoCapSet n L hL hn tri ht).card≤
      (twoCoreEdges n L (fun a => ofPredicate n L (tri a) hL (ht a))).card := by
  classical
  let G := fun a => ofPredicate n L (tri a) hL (ht a)
  let X := unmarkedFullTwoCapSet n L hL hn tri ht
  have heq : (∑ c∈X,UpperOpenMathCapHeavyTriples.coreDegree n L G c)=4*X.card := by
    calc
      (∑ c∈X,UpperOpenMathCapHeavyTriples.coreDegree n L G c)=(∑ c∈X,4) := by
        apply sum_congr rfl
        intro c hc
        exact (mem_filter.mp hc).2.2.1
      _=4*X.card := by simp [Nat.mul_comm]
  have hb := certificate_unmarked_incidence_bound n L hL hn tri hi ht alltriple
  change (∑ c∈X,UpperOpenMathCapHeavyTriples.coreDegree n L G c)≤(twoCoreEdges n L G).card at hb
  rw [heq] at hb
  exact hb

#print axioms certificate_unmarked_incidence_bound
#print axioms certificate_four_times_unmarked_card
end Kobon.UpperOpenMathAntipodalAdjacency
