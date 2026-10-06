import Kobon.UpperOpenMathAntipodalAdjacency
import Kobon.UpperOpenMathTripleCharts

/-! Full unmarked two-cap triples cannot touch normalized balanced two-cap
triples. The opposite continuation need only be an actual used side, and
the neighbor's missing triangular sector is never assumed present. -/
namespace Kobon.UpperOpenMathAntipodalBalancedAdjacency
open Cells FanGeometry UpperFan UpperVertexBudget UpperTriangleIncidence
  UpperSharedIncidence UpperCoreExtraction UpperOpenMathAntipodalTwoCapChart
  UpperOpenMathAntipodalStarDegree UpperOpenMathSectorRecords
  UpperOpenMathAntipodalAdjacency UpperOpenMathTripleCharts Finset
set_option maxHeartbeats 1000000

theorem cap_left_at {n : ℕ} {L : ℕ → Line ℝ} (f : Sectors n 3 L)
    (z : ZMod 6) (hz : z∈f.triangular) :
    affineEval (L (f.opposite z)) (f.point z)=0 := by
  simpa only [f.triangle_support z hz,f.triangle_left z hz] using (f.triangle z).Aq

theorem cap_right_at {n : ℕ} {L : ℕ → Line ℝ} (f : Sectors n 3 L)
    (z : ZMod 6) (hz : z∈f.triangular) :
    affineEval (L (f.opposite z)) (f.point (z+1))=0 := by
  simpa only [f.triangle_support z hz,f.triangle_right z hz] using (f.triangle z).Ar

theorem cap_avoids_at {n : ℕ} {L : ℕ → Line ℝ} (f : Sectors n 3 L)
    (z : ZMod 6) (hz : z∈f.triangular) :
    affineEval (L (f.opposite z)) f.center≠0 := by
  simpa only [f.triangle_support z hz,f.triangle_center z hz] using (f.triangle z).Ap

theorem cap_eq_selected {n : ℕ} {L : ℕ → Line ℝ} (f : Sectors n 3 L)
    (z : ZMod 6) (hp : z-1∈f.triangular) (hz : z∈f.triangular)
    (ho : OrdinaryAt n L (f.point z)) : f.opposite (z-1)=f.opposite z := by
  apply ordinary_nonradial_unique n L (f.point z) ho (f.radial z)
    (f.opposite (z-1)) (f.opposite z) (f.radial_point z)
  · simpa only [sub_add_cancel] using cap_right_at f (z-1) hp
  · exact cap_left_at f z hz
  · intro h
    exact cap_avoids_at f (z-1) hp (by rw [h]; exact f.radial_center z)
  · intro h
    exact cap_avoids_at f z hz (by rw [h]; exact f.radial_center z)

theorem normalized_selected {α : Type*} [Fintype α] (G : α → TriangleGeometry)
    {n : ℕ} {L : ℕ → Line ℝ} (g : Sectors n 3 L) (dg : NormalizedData G g)
    (z : ZMod 6) (hz : z∈({0,1,2,3,5} : Finset (ZMod 6))) : z∈g.triangular := by
  classical
  have ho0 := (g.mem_ordinaryShared 0).mp (by rw [dg.ordinary_eq]; simp)
  have ho3 := (g.mem_ordinaryShared 3).mp (by rw [dg.ordinary_eq]; simp)
  have hc1 : (1 : ZMod 6)∈g.coreShared := by rw [dg.core_eq]; simp
  have ht1 := (mem_filter.mp (mem_sdiff.mp hc1).1).1
  simp only [mem_insert,mem_singleton] at hz
  rcases hz with rfl|rfl|rfl|rfl|rfl
  · exact ho0.1
  · exact ht1
  · simpa using ho3.2.1
  · exact ho3.1
  · simpa using ho0.2.1

theorem radial_left_used {α : Type*} [Fintype α] (G : α → TriangleGeometry)
    {n : ℕ} {L : ℕ → Line ℝ} (g : Sectors n 3 L)
    (occ : ∀ z∈g.triangular, Nonempty (Occurrence G g.center g.point z))
    (z : ZMod 6) (hz : z∈g.triangular) : {g.center,g.point z}∈usedEdges G := by
  obtain ⟨o⟩ := occ z hz
  have h := transported_side_used G o.index o.triangle o.transport 0
  change ({o.triangle.p,o.triangle.q} : Edge)∈usedEdges G at h
  rw [o.center,o.left] at h
  exact h

theorem radial_right_used {α : Type*} [Fintype α] (G : α → TriangleGeometry)
    {n : ℕ} {L : ℕ → Line ℝ} (g : Sectors n 3 L)
    (occ : ∀ z∈g.triangular, Nonempty (Occurrence G g.center g.point z))
    (z : ZMod 6) (hz : z∈g.triangular) : {g.center,g.point (z+1)}∈usedEdges G := by
  obtain ⟨o⟩ := occ z hz
  have h := transported_side_used G o.index o.triangle o.transport 2
  change ({o.triangle.r,o.triangle.p} : Edge)∈usedEdges G at h
  rw [o.center,o.right] at h
  simpa only [pair_comm] using h

theorem normalized_right_pair_incompatible {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L)
    (tri : α → Triple) (ht : ∀ a, TrianglePredicate n L (tri a))
    (f g : Sectors n 3 L)
    (df : AntipodalData (fun a => ofPredicate n L (tri a) hL (ht a)) f)
    (dg : NormalizedData (fun a => ofPredicate n L (tri a) hL (ht a)) g)
    (center : g.center=f.point 1) (back : g.point 2=f.center)
    (right : g.point 1=f.point 2) (left : g.point 3=f.point 0)
    (triple : (supports n L (f.point 2)).card=3) : False := by
  classical
  let G := fun a => ofPredicate n L (tri a) hL (ht a)
  have gs (z : ZMod 6) (hz : z∈({0,1,2,3,5} : Finset (ZMod 6))) : z∈g.triangular :=
    normalized_selected G g dg z hz
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
    simpa using cap_eq_selected g 0 (by simpa using gs 5 (by decide)) (gs 0 (by decide)) go0
  have gh5 : affineEval (L (g.opposite 0)) (g.point 5)=0 := by
    rw [←geq50]
    exact cap_left_at g 5 (gs 5 (by decide))
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
    · exact cap_left_at g 1 (gs 1 (by decide))
    · simpa using cap_right_at g 1 (gs 1 (by decide))
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
    simpa using cap_right_at g 0 (gs 0 (by decide))
  have gmB : g.opposite 0≠f.opposite 1 := by
    intro he
    exact cap_avoids_at g 0 (gs 0 (by decide)) (by rw [he,center]; exact cap_left f df.triangular_eq 1)
  have gmC : g.opposite 0≠f.radial 2 := by
    intro he
    have hc : affineEval (L (g.opposite 0)) (g.point 2)=0 := by
      rw [he,back]; exact f.radial_center 2
    exact cap_avoids_at g 0 (gs 0 (by decide))
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
  have used := radial_left_used G g dg.occurrences 5 (gs 5 (by decide))
  exact block (by simpa only [center,point5] using used)


theorem normalized_left_pair_incompatible {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L)
    (tri : α → Triple) (ht : ∀ a, TrianglePredicate n L (tri a))
    (f g : Sectors n 3 L)
    (df : AntipodalData (fun a => ofPredicate n L (tri a) hL (ht a)) f)
    (dg : NormalizedData (fun a => ofPredicate n L (tri a) hL (ht a)) g)
    (center : g.center=f.point 2) (back : g.point 1=f.center)
    (neighbor : g.point 2=f.point 1)
    (triple : (supports n L (f.point 1)).card=3) : False := by
  classical
  let G := fun a => ofPredicate n L (tri a) hL (ht a)
  have gs (z : ZMod 6) (hz : z∈({0,1,2,3,5} : Finset (ZMod 6))) : z∈g.triangular :=
    normalized_selected G g dg z hz
  have fo0 : OrdinaryAt n L (f.point 0) :=
    ((f.mem_ordinaryShared 0).mp (by rw [df.ordinary_eq]; simp)).2.2
  have go3 : OrdinaryAt n L (g.point 3) :=
    ((g.mem_ordinaryShared 3).mp (by rw [dg.ordinary_eq]; simp)).2.2
  have feq50 : f.opposite 5=f.opposite 0 := by
    simpa using cap_eq_at_ordinary f df.triangular_eq 0 fo0
  have geq23 : g.opposite 2=g.opposite 3 := by
    simpa using cap_eq_selected g 3 (by simpa using gs 2 (by decide)) (gs 3 (by decide)) go3
  have gh4 : affineEval (L (g.opposite 2)) (g.point 4)=0 := by
    rw [geq23]
    simpa using cap_right_at g 3 (gs 3 (by decide))
  have fh5 : affineEval (L (f.opposite 0)) (f.point 5)=0 := by
    rw [←feq50]
    exact cap_left f df.triangular_eq 5
  have f25 : affineEval (L (f.radial 2)) (f.point 5)=0 := by
    simpa using antipodal_line_point f (L (f.radial 2)) 2
      (f.radial_center 2) (f.radial_point 2)
  have ge2 : g.radial 2=f.opposite 1 := by
    apply support_eq_of_two_points n L hL _ _ g.center (g.point 2) (dg.noncentral 2).symm
    · exact g.radial_center 2
    · exact g.radial_point 2
    · rw [center]; simpa using cap_right f df.triangular_eq 1
    · rw [neighbor]; exact cap_left f df.triangular_eq 1
  have ge1 : g.radial 1=f.radial 2 := by
    apply support_eq_of_two_points n L hL _ _ g.center (g.point 1) (dg.noncentral 1).symm
    · exact g.radial_center 1
    · exact g.radial_point 1
    · rw [center]; exact f.radial_point 2
    · rw [back]; exact f.radial_center 2
  have f11ne : f.radial 1≠f.opposite 1 := by
    intro he
    exact cap_avoids f df.triangular_eq 1 (by rw [←he]; exact f.radial_center 1)
  have f10ne : f.radial 1≠f.opposite 0 := by
    intro he
    exact cap_avoids f df.triangular_eq 0 (by rw [←he]; exact f.radial_center 1)
  have fcap_nonzero : affineEval (L (f.opposite 0)) (f.point 2)≠0 := by
    intro hp
    exact cap_avoids f df.triangular_eq 0
      (antipodal_line_center f (L (f.opposite 0)) 2 hp (by simpa using fh5))
  have fop_ne : f.opposite 1≠f.opposite 0 := by
    intro he
    exact fcap_nonzero (by rw [←he]; simpa using cap_right f df.triangular_eq 1)
  have gmA : affineEval (L (g.opposite 2)) (f.point 1)=0 := by
    rw [←neighbor]
    exact cap_left_at g 2 (gs 2 (by decide))
  have gmB : g.opposite 2≠f.opposite 1 := by
    intro he
    exact cap_avoids_at g 2 (gs 2 (by decide))
      (by rw [he,center]; simpa using cap_right f df.triangular_eq 1)
  have gmC : g.opposite 2≠f.radial 1 := by
    intro he
    have hc : affineEval (L (g.opposite 2)) (g.point 1)=0 := by
      rw [he,back]; exact f.radial_center 1
    exact cap_avoids_at g 2 (gs 2 (by decide))
      (antipodal_line_center g (L (g.opposite 2)) 1 hc (by simpa using gh4))
  have member (a : Fin n) (ha : affineEval (L a) (f.point 1)=0) :
      a∈supports n L (f.point 1) := by simp [supports,ha]
  have cases := mem_three_of_card_three (supports n L (f.point 1))
    (f.radial 1) (f.opposite 1) (f.opposite 0) (g.opposite 2) triple
    f11ne f10ne fop_ne (member _ (f.radial_point 1))
    (member _ (cap_left f df.triangular_eq 1))
    (member _ (by simpa using cap_right f df.triangular_eq 0)) (member _ gmA)
  have gcap2 : g.opposite 2=f.opposite 0 := cases.resolve_left gmC |>.resolve_left gmB
  have ghline : affineEval (L (f.radial 2)) (g.point 4)=0 := by
    rw [←ge1]
    simpa using antipodal_line_point g (L (g.radial 1)) 1 (g.radial_center 1) (g.radial_point 1)
  have ghcap : affineEval (L (f.opposite 0)) (g.point 4)=0 := by rw [←gcap2]; exact gh4
  have hradne : f.radial 2≠f.opposite 0 := by
    intro he
    exact cap_avoids f df.triangular_eq 0 (by rw [←he]; exact f.radial_center 2)
  have point4 : g.point 4=f.point 5 := two_lines_two_points _ _ _ _
    (det_ne_of_distinct n L hL _ _ hradne) ghline f25 ghcap fh5
  obtain ⟨_,block,_,_⟩ := certificate_star_blocks n L hL tri ht f df
  have used := radial_right_used G g dg.occurrences 3 (gs 3 (by decide))
  have used4 : {g.center,g.point 4}∈usedEdges G := by simpa using used
  exact block (by simpa only [center,point4] using used4)

theorem mixed_neighbor_matching {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (f g : Sectors n 3 L)
    (df : AntipodalData (fun a => ofPredicate n L (tri a) hL (ht a)) f)
    (dg : NormalizedData (fun a => ofPredicate n L (tri a) hL (ht a)) g)
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
  have gshared := (mem_sdiff.mp hw).1
  obtain ⟨o⟩ := df.occurrences (z-1) (by rw [df.triangular_eq]; simp)
  obtain ⟨p⟩ := df.occurrences z (by rw [df.triangular_eq]; simp)
  obtain ⟨a⟩ := dg.occurrences (w-1) (mem_filter.mp gshared).2
  obtain ⟨b⟩ := dg.occurrences w (mem_filter.mp gshared).1
  have disjoint : Pairwise (fun a b => Disjoint (G a).interior (G b).interior) := by
    intro a b hab
    exact distinct_interiors_disjoint n L _ _ hL (ht a) (ht b) (fun h=>hab (hi h))
  have hmatch := UpperOpenMathFiberMatching.neighboring_points_match G disjoint
    (by decide : 2≤3) (by decide : 2≤3) f.center g.center f.point g.point
    df.injective dg.injective df.noncentral dg.noncentral df.positive dg.positive
    z w center hc o p a b
  exact ⟨w,hw,hc,hmatch⟩

theorem first_ray_mixed_incompatible {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (f g : Sectors n 3 L)
    (df : AntipodalData (fun a => ofPredicate n L (tri a) hL (ht a)) f)
    (dg : NormalizedData (fun a => ofPredicate n L (tri a) hL (ht a)) g)
    (alltriple : ∀ c∈core n L, (supports n L c).card=3)
    (center : g.center=f.point 1) : False := by
  classical
  let G := fun a => ofPredicate n L (tri a) hL (ht a)
  obtain ⟨w,hw,hback,hr,hl⟩ := mixed_neighbor_matching n L hL tri hi ht f g df dg 1
    (by rw [df.core_eq]; simp) center
  have ordinary : OrdinaryAt n L (g.point (w+1)) := by
    rw [hl]
    simpa using ((f.mem_ordinaryShared 0).mp (by rw [df.ordinary_eq]; simp)).2.2
  have hwcase : w=1∨w=2 := by simpa only [dg.core_eq,mem_insert,mem_singleton] using hw
  have hnext : w+1∈g.triangular := by
    rcases hwcase with h|h
    · rw [h]; simpa using normalized_selected G g dg 2 (by decide)
    · rw [h]; simpa using normalized_selected G g dg 3 (by decide)
  have hrest : w+1-1∈g.triangular := by simpa using (mem_filter.mp (mem_sdiff.mp hw).1).1
  have hord : w+1∈g.ordinaryShared := (g.mem_ordinaryShared (w+1)).mpr ⟨hnext,hrest,ordinary⟩
  have hO : w+1=0∨w+1=3 := by simpa only [dg.ordinary_eq,mem_insert,mem_singleton] using hord
  have hw2 : w=2 := (by decide : ∀ w : ZMod 6,
    (w=1∨w=2) → (w+1=0∨w+1=3) → w=2) w hwcase hO
  subst w
  exact normalized_right_pair_incompatible n L hL tri ht f g df dg center hback
    (by simpa using hr) (by simpa using hl)
    (alltriple _ (df.core_endpoint 2 (by rw [df.core_eq]; simp)))

theorem second_ray_mixed_incompatible {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (f g : Sectors n 3 L)
    (df : AntipodalData (fun a => ofPredicate n L (tri a) hL (ht a)) f)
    (dg : NormalizedData (fun a => ofPredicate n L (tri a) hL (ht a)) g)
    (alltriple : ∀ c∈core n L, (supports n L c).card=3)
    (center : g.center=f.point 2) : False := by
  classical
  let G := fun a => ofPredicate n L (tri a) hL (ht a)
  obtain ⟨w,hw,hback,hr,hl⟩ := mixed_neighbor_matching n L hL tri hi ht f g df dg 2
    (by rw [df.core_eq]; simp) center
  have ordinary : OrdinaryAt n L (g.point (w-1)) := by
    rw [hr]
    simpa using ((f.mem_ordinaryShared 3).mp (by rw [df.ordinary_eq]; simp)).2.2
  have hwcase : w=1∨w=2 := by simpa only [dg.core_eq,mem_insert,mem_singleton] using hw
  have hprev : w-1∈g.triangular := (mem_filter.mp (mem_sdiff.mp hw).1).2
  have hprevprev : w-1-1∈g.triangular := by
    rcases hwcase with h|h
    · rw [h]; simpa using normalized_selected G g dg 5 (by decide)
    · rw [h]; simpa using normalized_selected G g dg 0 (by decide)
  have hord : w-1∈g.ordinaryShared := (g.mem_ordinaryShared (w-1)).mpr ⟨hprev,hprevprev,ordinary⟩
  have hO : w-1=0∨w-1=3 := by simpa only [dg.ordinary_eq,mem_insert,mem_singleton] using hord
  have hw1 : w=1 := (by decide : ∀ w : ZMod 6,
    (w=1∨w=2) → (w-1=0∨w-1=3) → w=1) w hwcase hO
  subst w
  exact normalized_left_pair_incompatible n L hL tri ht f g df dg center hback
    (by simpa using hl)
    (alltriple _ (df.core_endpoint 1 (by rw [df.core_eq]; simp)))

theorem mixed_charts_not_adjacent {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (f g : Sectors n 3 L)
    (df : AntipodalData (fun a => ofPredicate n L (tri a) hL (ht a)) f)
    (dg : NormalizedData (fun a => ofPredicate n L (tri a) hL (ht a)) g)
    (alltriple : ∀ c∈core n L, (supports n L c).card=3)
    (z : ZMod 6) (hz : z∈f.coreShared) (center : g.center=f.point z) : False := by
  classical
  let G := fun a => ofPredicate n L (tri a) hL (ht a)
  have hcase : z=1∨z=2∨z=4∨z=5 := by simpa only [df.core_eq,mem_insert,mem_singleton] using hz
  rcases hcase with rfl|rfl|rfl|rfl
  · exact first_ray_mixed_incompatible n L hL tri hi ht f g df dg alltriple center
  · exact second_ray_mixed_incompatible n L hL tri hi ht f g df dg alltriple center
  · let f' := UpperOpenMathRotation.Sectors.shift f 3
    have df' := shift_three_data G f df
    apply first_ray_mixed_incompatible n L hL tri hi ht f' g df' dg alltriple
    simpa [f'] using center
  · let f' := UpperOpenMathRotation.Sectors.shift f 3
    have df' := shift_three_data G f df
    apply second_ray_mixed_incompatible n L hL tri hi ht f' g df' dg alltriple
    simpa [f'] using center

#print axioms normalized_right_pair_incompatible
#print axioms normalized_left_pair_incompatible
#print axioms mixed_neighbor_matching
#print axioms mixed_charts_not_adjacent

/-- A full unmarked two-cap core cannot touch an unmarked balanced two-cap
core in an actual all-triple arrangement. The missing neighbor sector is
kept missing throughout the proof. -/
theorem certificate_unmarked_full_balanced_not_adjacent {α : Type*} [Fintype α]
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
      (fun a => ofPredicate n L (tri a) hL (ht a)) d=2)
    (zc : UpperOpenMathMarkedPorts.markedCount n L hL hn tri ht c=0)
    (zd : UpperOpenMathMarkedPorts.markedCount n L hL hn tri ht d=0)
    (edge : {c,d}∈twoCoreEdges n L (fun a => ofPredicate n L (tri a) hL (ht a))) : False := by
  classical
  let G := fun a => ofPredicate n L (tri a) hL (ht a)
  obtain ⟨f,hfc,df⟩ := certificate_antipodal_chart n L hL hn tri hi ht c hc
    (alltriple c hc) ac dc zc
  obtain ⟨g,hgd,dg⟩ := UpperOpenMathMarkedPorts.certificate_normalized_two_two_of_zero_marks
    n L hL hn tri hi ht d hd (alltriple d hd) ad dd zd
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
  exact mixed_charts_not_adjacent n L hL tri hi ht f g df dg alltriple z hz center

#print axioms certificate_unmarked_full_balanced_not_adjacent
end Kobon.UpperOpenMathAntipodalBalancedAdjacency
