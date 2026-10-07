import Kobon.UpperOpenMathAntipodalBalancedAdjacency

/-! Adjacent outer cores of an antipodal two-cap star cannot both have
full triangular fans. Each full neighbor would force the same intersection
of the ordinary axis and their common cap to lie on two incompatible
outward rays. Ordinary degrees of the neighbors are unrestricted.
-/
namespace Kobon.UpperOpenMathAntipodalFullNeighborPair
open Cells FanGeometry UpperFan UpperVertexBudget UpperTriangleIncidence
  UpperSharedIncidence UpperCoreExtraction UpperOpenMathAntipodalTwoCapChart
  UpperOpenMathAntipodalStarDegree UpperOpenMathSectorRecords
  UpperOpenMathAntipodalAdjacency UpperOpenMathAntipodalBalancedAdjacency Finset
set_option maxHeartbeats 1000000

theorem outward_antipodes_ne (p q u v : Point) (s t : ℝ)
    (hs : 0<s) (ht : 0<t) (hpq : p≠q)
    (hu : u=(p.1-s*(q.1-p.1),p.2-s*(q.2-p.2)))
    (hv : v=(q.1-t*(p.1-q.1),q.2-t*(p.2-q.2))) : u≠v := by
  intro he
  have ha : 1+s+t≠0 := by linarith
  have hx : (1+s+t)*(p.1-q.1)=0 := by
    have hx := congrArg Prod.fst he
    rw [hu,hv] at hx
    dsimp at hx
    nlinarith
  have hy : (1+s+t)*(p.2-q.2)=0 := by
    have hy := congrArg Prod.snd he
    rw [hu,hv] at hy
    dsimp at hy
    nlinarith
  exact hpq (Prod.ext (sub_eq_zero.mp ((mul_eq_zero.mp hx).resolve_left ha))
    (sub_eq_zero.mp ((mul_eq_zero.mp hy).resolve_left ha)))

theorem matched_full_neighbor_pair_impossible {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L)
    (tri : α → Triple) (ht : ∀ a, TrianglePredicate n L (tri a))
    (f g k : Sectors n 3 L)
    (df : AntipodalData (fun a => ofPredicate n L (tri a) hL (ht a)) f)
    (gfull : g.triangular=univ) (kfull : k.triangular=univ)
    (w x : ZMod 6)
    (gc : g.center=f.point 1) (gp : g.point w=f.center)
    (gr : g.point (w-1)=f.point 2) (gl : g.point (w+1)=f.point 0)
    (kc : k.center=f.point 2) (kp : k.point x=f.center)
    (kr : k.point (x-1)=f.point 3) (kl : k.point (x+1)=f.point 1) : False := by
  classical
  have hgp0 : OrdinaryAt n L (g.point (w+1)) := by
    rw [gl]
    exact ((f.mem_ordinaryShared 0).mp (by rw [df.ordinary_eq]; simp)).2.2
  have hkp3 : OrdinaryAt n L (k.point (x-1)) := by
    rw [kr]
    exact ((f.mem_ordinaryShared 3).mp (by rw [df.ordinary_eq]; simp)).2.2
  have gwcap : g.opposite w=g.opposite (w+1) := by
    simpa using cap_eq_at_ordinary g gfull (w+1) hgp0
  have kxcap : k.opposite (x-2)=k.opposite (x-1) := by
    have hi : x-1-1=x-2 := by ring
    simpa only [hi] using cap_eq_at_ordinary k kfull (x-1) hkp3
  have f03 : affineEval (L (f.radial 0)) (f.point 3)=0 := by
    simpa using antipodal_line_point f (L (f.radial 0)) 0
      (f.radial_center 0) (f.radial_point 0)
  have gaxis : g.opposite w=f.radial 0 := by
    apply support_eq_of_two_points n L hL _ _ f.center (f.point 0) (df.noncentral 0).symm
    · rw [←gp]; exact cap_left g gfull w
    · rw [←gl]; exact cap_right g gfull w
    · exact f.radial_center 0
    · exact f.radial_point 0
  have kaxis : k.opposite (x-1)=f.radial 0 := by
    apply support_eq_of_two_points n L hL _ _ f.center (f.point 3) (df.noncentral 3).symm
    · rw [←kp]; simpa only [sub_add_cancel] using cap_right k kfull (x-1)
    · rw [←kr]; exact cap_left k kfull (x-1)
    · exact f.radial_center 0
    · exact f03
  have hi1 : (w+1)+1=w+2 := by ring
  have hi2 : (w-1)+3=w+2 := by ring
  have hi3 : (x+1)+3=x-2 := (by decide : ∀ x : ZMod 6, (x+1)+3=x-2) x
  have gA : affineEval (L (f.radial 0)) (g.point (w+2))=0 := by
    rw [←gaxis,gwcap]
    simpa only [hi1] using cap_right g gfull (w+1)
  have kA : affineEval (L (f.radial 0)) (k.point (x-2))=0 := by
    rw [←kaxis,←kxcap]
    exact cap_left k kfull (x-2)
  have gR : affineEval (L (f.opposite 1)) (g.point (w+2))=0 := by
    have h := antipodal_line_point g (L (f.opposite 1)) (w-1)
      (by rw [gc]; exact cap_left f df.triangular_eq 1)
      (by rw [gr]; simpa using cap_right f df.triangular_eq 1)
    simpa only [hi2] using h
  have kR : affineEval (L (f.opposite 1)) (k.point (x-2))=0 := by
    have h := antipodal_line_point k (L (f.opposite 1)) (x+1)
      (by rw [kc]; simpa using cap_right f df.triangular_eq 1)
      (by rw [kl]; exact cap_left f df.triangular_eq 1)
    simpa only [hi3] using h
  have neq : f.radial 0≠f.opposite 1 := by
    intro he
    exact cap_avoids f df.triangular_eq 1 (by rw [←he]; exact f.radial_center 0)
  have equal : g.point (w+2)=k.point (x-2) := two_lines_two_points _ _ _ _
    (det_ne_of_distinct n L hL _ _ neq) gA kA gR kR
  obtain ⟨s,hs,he⟩ := g.antipodal (w-1)
  obtain ⟨t,ht,he'⟩ := k.antipodal (x+1)
  simp only [Nat.cast_ofNat,hi2,gc,gr] at he
  simp only [Nat.cast_ofNat,hi3,kc,kl] at he'
  exact outward_antipodes_ne (f.point 1) (f.point 2) _ _ s t hs ht
    (fun h=>(by decide : (1 : ZMod 6)≠2) (df.injective h)) he he' equal

#print axioms matched_full_neighbor_pair_impossible

structure AnyChartData {α : Type*} [Fintype α] (G : α → TriangleGeometry)
    {n : ℕ} {L : ℕ → Line ℝ} (f : Sectors n 3 L) : Prop where
  injective : Function.Injective f.point
  noncentral : ∀ z, f.point z≠f.center
  positive : ∀ z, 0<areaDet f.center (f.point z) (f.point (z+1))
  core_image : f.coreShared.image (fun z => ({f.center,f.point z} : Edge))=
    (twoCoreEdges n L G).filter (fun e => f.center∈e)
  occurrences : ∀ z∈f.triangular, Nonempty (Occurrence G f.center f.point z)

theorem lift_three_chart {α : Type*} [Fintype α] (G : α → TriangleGeometry)
    {n r : ℕ} [NeZero (2*r)] {L : ℕ → Line ℝ} (f : Sectors n r L) (hr : r=3)
    (inj : Function.Injective f.point) (nc : ∀ z, f.point z≠f.center)
    (pos : ∀ z, 0<areaDet f.center (f.point z) (f.point (z+1)))
    (im : f.coreShared.image (fun z => ({f.center,f.point z} : Edge))=
      (twoCoreEdges n L G).filter (fun e => f.center∈e))
    (occ : ∀ z∈f.triangular, Nonempty (Occurrence G f.center f.point z)) :
    ∃ g : Sectors n 3 L, g.center=f.center ∧ AnyChartData G g ∧
      (f.triangular=univ → g.triangular=univ) := by
  subst r
  exact ⟨f,rfl,⟨inj,nc,pos,im,occ⟩,fun h=>h⟩

noncomputable def FullAt {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (G : α → TriangleGeometry) (c : Point) : Prop :=
  UpperOpenMathCapHeavyTriples.ordinaryDegree n L G c+
    UpperOpenMathCapHeavyTriples.coreDegree n L G c=6

theorem certificate_any_triple_chart {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (c : Point) (hc : c∈core n L) (rc : (supports n L c).card=3) :
    let G := fun a => ofPredicate n L (tri a) hL (ht a)
    ∃ g : Sectors n 3 L, g.center=c ∧ AnyChartData G g ∧
      (FullAt n L G c → g.triangular=univ) := by
  classical
  let G := fun a => ofPredicate n L (tri a) hL (ht a)
  letI : NeZero (2*(supports n L c).card) := ⟨by omega⟩
  let D := UpperOpenMathRadialOrder.atPoint n L hL hn c
  let f := UpperOpenMathActualFans.fan n L hL hn tri ht c (mem_filter.mp hc).1 D (by omega)
  have occ : ∀ z∈f.triangular, Nonempty (Occurrence G f.center f.point z) := by
    intro z hz
    exact (mem_triangular G c f.point z).mp hz
  have hfull : FullAt n L G c → f.triangular=univ := by
    intro full
    apply UpperOpenMathFullSharing.shared_full f
    have hs := f.shared_card_split
    rw [UpperOpenMathActualFans.fan_ordinary_card n L hL hn tri ht c
      (mem_filter.mp hc).1 D (by omega) hi hc,
      UpperOpenMathActualFans.fan_core_card n L hL hn tri ht c
      (mem_filter.mp hc).1 D (by omega) hi hc] at hs
    change UpperOpenMathCapHeavyTriples.ordinaryDegree n L G c+
      UpperOpenMathCapHeavyTriples.coreDegree n L G c=f.shared.card at hs
    change f.shared.card=2*(supports n L c).card
    change UpperOpenMathCapHeavyTriples.ordinaryDegree n L G c+
      UpperOpenMathCapHeavyTriples.coreDegree n L G c=6 at full
    omega
  obtain ⟨g,hg,dg,hcast⟩ := lift_three_chart G f rc
    (UpperOpenMathActualFans.fan_point_injective n L hL hn tri ht c (mem_filter.mp hc).1 D (by omega))
    (UpperOpenMathActualFans.fan_point_ne_center n L hL hn tri ht c (mem_filter.mp hc).1 D (by omega))
    (UpperOpenMathActualFans.fan_positive n L hL hn tri ht c (mem_filter.mp hc).1 D (by omega))
    (UpperOpenMathActualFans.fan_core_image n L hL hn tri ht c (mem_filter.mp hc).1 D (by omega) hi hc)
    occ
  exact ⟨g,hg,dg,fun h=>hcast (hfull h)⟩

theorem any_chart_neighbor_matching {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (f g : Sectors n 3 L)
    (df : AntipodalData (fun a => ofPredicate n L (tri a) hL (ht a)) f)
    (dg : AnyChartData (fun a => ofPredicate n L (tri a) hL (ht a)) g)
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

/-- The ordinary degrees of the two outer neighbors are unrestricted. -/
theorem chart_first_pair_not_full {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (alltriple : ∀ c∈core n L, (supports n L c).card=3)
    (f : Sectors n 3 L)
    (df : AntipodalData (fun a => ofPredicate n L (tri a) hL (ht a)) f) :
    let G := fun a => ofPredicate n L (tri a) hL (ht a)
    ¬(FullAt n L G (f.point 1)∧FullAt n L G (f.point 2)) := by
  classical
  let G := fun a => ofPredicate n L (tri a) hL (ht a)
  change ¬(FullAt n L G (f.point 1)∧FullAt n L G (f.point 2))
  rintro ⟨full1,full2⟩
  have hc1 := df.core_endpoint 1 (by rw [df.core_eq]; simp)
  have hc2 := df.core_endpoint 2 (by rw [df.core_eq]; simp)
  obtain ⟨g,gc,dg,hfullg⟩ := certificate_any_triple_chart n L hL hn tri hi ht
    (f.point 1) hc1 (alltriple _ hc1)
  obtain ⟨k,kc,dk,hfullk⟩ := certificate_any_triple_chart n L hL hn tri hi ht
    (f.point 2) hc2 (alltriple _ hc2)
  obtain ⟨w,hw,gp,gr,gl⟩ := any_chart_neighbor_matching n L hL tri hi ht f g df dg 1
    (by rw [df.core_eq]; simp) gc
  obtain ⟨x,hx,kp,kr,kl⟩ := any_chart_neighbor_matching n L hL tri hi ht f k df dk 2
    (by rw [df.core_eq]; simp) kc
  exact matched_full_neighbor_pair_impossible n L hL tri ht f g k df
    (hfullg full1) (hfullk full2) w x gc gp (by simpa using gr) (by simpa using gl)
    kc kp (by simpa using kr) (by simpa using kl)

theorem chart_second_pair_not_full {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (alltriple : ∀ c∈core n L, (supports n L c).card=3)
    (f : Sectors n 3 L)
    (df : AntipodalData (fun a => ofPredicate n L (tri a) hL (ht a)) f) :
    let G := fun a => ofPredicate n L (tri a) hL (ht a)
    ¬(FullAt n L G (f.point 4)∧FullAt n L G (f.point 5)) := by
  classical
  let G := fun a => ofPredicate n L (tri a) hL (ht a)
  let f' := UpperOpenMathRotation.Sectors.shift f 3
  have h := chart_first_pair_not_full n L hL hn tri hi ht alltriple f'
    (shift_three_data G f df)
  simpa [f'] using h

#print axioms certificate_any_triple_chart
#print axioms chart_first_pair_not_full
#print axioms chart_second_pair_not_full

noncomputable def FullTripleAt {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (G : α → TriangleGeometry) (c : Point) : Prop :=
  (supports n L c).card=3 ∧ FullAt n L G c

/-- Only the two proposed full neighbors need to be triples. -/
theorem chart_first_pair_not_full_triples {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (f : Sectors n 3 L)
    (df : AntipodalData (fun a => ofPredicate n L (tri a) hL (ht a)) f) :
    let G := fun a => ofPredicate n L (tri a) hL (ht a)
    ¬(FullTripleAt n L G (f.point 1)∧FullTripleAt n L G (f.point 2)) := by
  classical
  let G := fun a => ofPredicate n L (tri a) hL (ht a)
  change ¬(FullTripleAt n L G (f.point 1)∧FullTripleAt n L G (f.point 2))
  rintro ⟨⟨r1,full1⟩,⟨r2,full2⟩⟩
  have hc1 := df.core_endpoint 1 (by rw [df.core_eq]; simp)
  have hc2 := df.core_endpoint 2 (by rw [df.core_eq]; simp)
  obtain ⟨g,gc,dg,hfullg⟩ := certificate_any_triple_chart n L hL hn tri hi ht (f.point 1) hc1 r1
  obtain ⟨k,kc,dk,hfullk⟩ := certificate_any_triple_chart n L hL hn tri hi ht (f.point 2) hc2 r2
  obtain ⟨w,hw,gp,gr,gl⟩ := any_chart_neighbor_matching n L hL tri hi ht f g df dg 1
    (by rw [df.core_eq]; simp) gc
  obtain ⟨x,hx,kp,kr,kl⟩ := any_chart_neighbor_matching n L hL tri hi ht f k df dk 2
    (by rw [df.core_eq]; simp) kc
  exact matched_full_neighbor_pair_impossible n L hL tri ht f g k df
    (hfullg full1) (hfullk full2) w x gc gp (by simpa using gr) (by simpa using gl)
    kc kp (by simpa using kr) (by simpa using kl)

theorem chart_second_pair_not_full_triples {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (f : Sectors n 3 L)
    (df : AntipodalData (fun a => ofPredicate n L (tri a) hL (ht a)) f) :
    let G := fun a => ofPredicate n L (tri a) hL (ht a)
    ¬(FullTripleAt n L G (f.point 4)∧FullTripleAt n L G (f.point 5)) := by
  classical
  let G := fun a => ofPredicate n L (tri a) hL (ht a)
  let f' := UpperOpenMathRotation.Sectors.shift f 3
  have h := chart_first_pair_not_full_triples n L hL hn tri hi ht f' (shift_three_data G f df)
  simpa [f'] using h

noncomputable def nonFullTripleNeighbors {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (G : α → TriangleGeometry) (c : Point) : Finset Point := by
  classical
  exact (core n L).filter fun q=>{c,q}∈twoCoreEdges n L G ∧ ¬FullTripleAt n L G q

/-- At least two actual core neighbors are nonfull triples or higher cores. -/
theorem certificate_two_nonfull_or_higher_neighbors {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (c : Point) (hc : c∈core n L) (rc : (supports n L c).card=3)
    (ac : UpperOpenMathCapHeavyTriples.ordinaryDegree n L
      (fun a => ofPredicate n L (tri a) hL (ht a)) c=2)
    (dc : UpperOpenMathCapHeavyTriples.coreDegree n L
      (fun a => ofPredicate n L (tri a) hL (ht a)) c=4)
    (zc : UpperOpenMathMarkedPorts.markedCount n L hL hn tri ht c=0) :
    2≤(nonFullTripleNeighbors n L (fun a => ofPredicate n L (tri a) hL (ht a)) c).card := by
  classical
  let G := fun a => ofPredicate n L (tri a) hL (ht a)
  obtain ⟨f,hfc,df⟩ := certificate_antipodal_chart n L hL hn tri hi ht c hc rc ac dc zc
  have hfirst := chart_first_pair_not_full_triples n L hL hn tri hi ht f df
  have hsecond := chart_second_pair_not_full_triples n L hL hn tri hi ht f df
  have choose1 : ∃ a : ZMod 6, a∈({1,2} : Finset (ZMod 6)) ∧ ¬FullTripleAt n L G (f.point a) := by
    by_cases h : FullTripleAt n L G (f.point 1)
    · exact ⟨2,by simp,fun h2=>hfirst ⟨h,h2⟩⟩
    · exact ⟨1,by simp,h⟩
  have choose2 : ∃ b : ZMod 6, b∈({4,5} : Finset (ZMod 6)) ∧ ¬FullTripleAt n L G (f.point b) := by
    by_cases h : FullTripleAt n L G (f.point 4)
    · exact ⟨5,by simp,fun h5=>hsecond ⟨h,h5⟩⟩
    · exact ⟨4,by simp,h⟩
  obtain ⟨a,ha,na⟩ := choose1
  obtain ⟨b,hb,nb⟩ := choose2
  have hac : a∈f.coreShared := by
    rw [df.core_eq]
    simp only [mem_insert,mem_singleton] at ha ⊢
    tauto
  have hbc : b∈f.coreShared := by
    rw [df.core_eq]
    simp only [mem_insert,mem_singleton] at hb ⊢
    tauto
  have hab : a≠b := by
    have sep := (by decide : ∀ a b : ZMod 6,
      a∈({1,2} : Finset (ZMod 6)) → b∈({4,5} : Finset (ZMod 6)) → a≠b)
    exact sep a b ha hb
  have pointsNe : f.point a≠f.point b := fun he=>hab (df.injective he)
  have ma : f.point a∈nonFullTripleNeighbors n L G c := by
    apply mem_filter.mpr
    refine ⟨df.core_endpoint a hac,?_,na⟩
    simpa only [hfc] using core_edge_of_label G f df.toFullData a hac
  have mb : f.point b∈nonFullTripleNeighbors n L G c := by
    apply mem_filter.mpr
    refine ⟨df.core_endpoint b hbc,?_,nb⟩
    simpa only [hfc] using core_edge_of_label G f df.toFullData b hbc
  have sub : ({f.point a,f.point b} : Finset Point)⊆nonFullTripleNeighbors n L G c := by
    intro q hq
    rcases mem_insert.mp hq with rfl|hq
    · exact ma
    · simpa only [mem_singleton.mp hq] using mb
  have card := card_le_card sub
  rw [card_pair pointsNe] at card
  exact card

#print axioms chart_first_pair_not_full_triples
#print axioms certificate_two_nonfull_or_higher_neighbors
end Kobon.UpperOpenMathAntipodalFullNeighborPair
