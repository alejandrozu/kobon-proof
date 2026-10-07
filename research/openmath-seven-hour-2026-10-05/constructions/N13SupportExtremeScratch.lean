import Kobon.UpperOpenMathN13NoDouble
import Kobon.UpperOpenMathCoreComponents

namespace Kobon.UpperOpenMathN13SupportExtreme
open Cells FanGeometry UpperFan UpperVertexBudget UpperCoreExtraction UpperSharedIncidence UpperTriangleIncidence
  UpperOpenMathAntipodalAdjacency UpperOpenMathAntipodalTwoCapChart
  UpperOpenMathN13ExtractionHelpers UpperOpenMathCoreComponents Finset
set_option maxHeartbeats 2000000

theorem same_sign_coeff_max_equal (a b u v : ℝ) (hab : 0<a*b)
    (hu : u≤0) (hv : v≤0) (he : a*u+b*v=0) : u=0 := by
  rcases mul_pos_iff.mp hab with ⟨ha,hb⟩|⟨ha,hb⟩
  · have h1 := mul_nonpos_of_nonneg_of_nonpos ha.le hu
    have h2 := mul_nonpos_of_nonneg_of_nonpos hb.le hv
    have hz : a*u=0 := by linarith
    exact (mul_eq_zero.mp hz).resolve_left ha.ne'
  · have h1 := mul_nonneg_of_nonpos_of_nonpos ha.le hu
    have h2 := mul_nonneg_of_nonpos_of_nonpos hb.le hv
    have hz : a*u=0 := by linarith
    exact (mul_eq_zero.mp hz).resolve_left ha.ne

/-- A collinear pair on opposite sides of c cannot both lie below c for
    an affine functional injective on the relevant finite point set. -/
theorem collinear_max_equal (c d p q : Point) (w : Line ℝ)
    (col : areaDet p c q=0)
    (opposite : areaDet c d p*areaDet c d q<0)
    (hp : affineEval w p≤affineEval w c) (hq : affineEval w q≤affineEval w c) :
    affineEval w p=affineEval w c := by
  have hi := UpperFanSupport.affine_area_identity w d p c q
  rw [col,zero_mul] at hi
  have ha : areaDet d c q= -areaDet c d q := by dsimp [areaDet]; ring
  have hb : areaDet d p c=areaDet c d p := by dsimp [areaDet]; ring
  have positive : 0<areaDet d c q*areaDet d p c := by rw [ha,hb]; nlinarith
  exact sub_eq_zero.mp (same_sign_coeff_max_equal _ _ _ _ positive
    (sub_nonpos.mpr hp) (sub_nonpos.mpr hq) hi)

private theorem previous_core {α : Type*} [Fintype α]
    {n : ℕ} {L : ℕ → Line ℝ} (G : α → TriangleGeometry)
    (g : Sectors n 3 L) (dg : AntipodalData G g) (w : ZMod 6)
    (hw : w∈g.coreShared) (ho : OrdinaryAt n L (g.point (w-1))) : w-2∈g.coreShared := by
  classical
  have hm : w-1∈g.ordinaryShared := (g.mem_ordinaryShared (w-1)).mpr
    ⟨by rw [dg.triangular_eq]; simp,by rw [dg.triangular_eq]; simp,ho⟩
  have rule : ∀ w : ZMod 6, w∈({1,2,4,5} : Finset (ZMod 6)) →
      w-1∈({0,3} : Finset (ZMod 6)) → w-2∈({1,2,4,5} : Finset (ZMod 6)) := by decide
  rw [dg.core_eq]
  rw [dg.core_eq] at hw
  rw [dg.ordinary_eq] at hm
  exact rule w hw hm

private theorem next_core {α : Type*} [Fintype α]
    {n : ℕ} {L : ℕ → Line ℝ} (G : α → TriangleGeometry)
    (g : Sectors n 3 L) (dg : AntipodalData G g) (w : ZMod 6)
    (hw : w∈g.coreShared) (ho : OrdinaryAt n L (g.point (w+1))) : w+2∈g.coreShared := by
  classical
  have hm : w+1∈g.ordinaryShared := (g.mem_ordinaryShared (w+1)).mpr
    ⟨by rw [dg.triangular_eq]; simp,by rw [dg.triangular_eq]; simp,ho⟩
  have rule : ∀ w : ZMod 6, w∈({1,2,4,5} : Finset (ZMod 6)) →
      w+1∈({0,3} : Finset (ZMod 6)) → w+2∈({1,2,4,5} : Finset (ZMod 6)) := by decide
  rw [dg.core_eq]
  rw [dg.core_eq] at hw
  rw [dg.ordinary_eq] at hm
  exact rule w hw hm

private theorem previous_on_line {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (G : α → TriangleGeometry)
    (g : Sectors n 3 L) (dg : AntipodalData G g) (w : ZMod 6)
    (ho : OrdinaryAt n L (g.point (w-1))) (i : Fin n)
    (hc : affineEval (L i) (g.point w)=0)
    (hp : affineEval (L i) (g.point (w-1))=0) :
    affineEval (L i) (g.point (w-2))=0 := by
  have hi : w-1-1=w-2 := by ring
  have he : g.opposite (w-2)=g.opposite (w-1) := by
    simpa only [hi] using cap_eq_at_ordinary g dg.triangular_eq (w-1) ho
  have neq : g.point (w-1)≠g.point w := by
    intro h
    exact (by intro h; exact (by decide : (1 : ZMod 6)≠0) (sub_eq_self.mp h) : w-1≠w) (dg.injective h)
  have cap : g.opposite (w-1)=i := support_eq_of_two_points n L hL _ _ _ _ neq
    (cap_left g dg.triangular_eq (w-1))
    (by simpa only [sub_add_cancel] using cap_right g dg.triangular_eq (w-1)) hp hc
  rw [←cap,←he]
  exact cap_left g dg.triangular_eq (w-2)

private theorem next_on_line {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (G : α → TriangleGeometry)
    (g : Sectors n 3 L) (dg : AntipodalData G g) (w : ZMod 6)
    (ho : OrdinaryAt n L (g.point (w+1))) (i : Fin n)
    (hc : affineEval (L i) (g.point w)=0)
    (hp : affineEval (L i) (g.point (w+1))=0) :
    affineEval (L i) (g.point (w+2))=0 := by
  have he : g.opposite w=g.opposite (w+1) := by
    simpa only [add_sub_cancel_right] using cap_eq_at_ordinary g dg.triangular_eq (w+1) ho
  have neq : g.point w≠g.point (w+1) := by
    intro h
    have hi := dg.injective h
    exact (by decide : (1 : ZMod 6)≠0) (add_eq_left.mp hi.symm)
  have cap : g.opposite w=i := support_eq_of_two_points n L hL _ _ _ _ neq
    (cap_left g dg.triangular_eq w) (cap_right g dg.triangular_eq w) hc hp
  rw [←cap,he]
  have hi : w+1+1=w+2 := by ring
  simpa only [hi] using cap_right g dg.triangular_eq (w+1)

private theorem point_mem_closed {α : Type*} [Fintype α]
    {n : ℕ} {L : ℕ → Line ℝ} (G : α → TriangleGeometry)
    (g : Sectors n 3 L) (dg : AntipodalData G g) (w z : ZMod 6)
    (hw : w∈g.coreShared) (hz : z∈g.coreShared)
    (P : Finset Point) (closed : SharedCoreClosed n L G P)
    (back : g.point w∈P) : g.point z∈P := by
  have ew := core_edge_of_label G g dg.toFullData w hw
  have ez := core_edge_of_label G g dg.toFullData z hz
  have center : g.center∈P := (closed _ ew (g.point w) (by simp) back) (by simp)
  exact (closed _ ez g.center (by simp) center) (by simp)

theorem previous_core_escape_not_max {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (G : α → TriangleGeometry) (g : Sectors n 3 L) (dg : AntipodalData G g)
    (w : ZMod 6) (hw : w∈g.coreShared) (ho : OrdinaryAt n L (g.point (w-1)))
    (i : Fin n) (p : Point)
    (hc : affineEval (L i) (g.point w)=0)
    (hp : affineEval (L i) (g.point (w-1))=0) (pp : affineEval (L i) p=0)
    (opposite : areaDet (g.point w) (g.point (w+1)) p*
      areaDet (g.point w) (g.point (w+1)) g.center<0)
    (P : Finset Point) (closed : SharedCoreClosed n L G P)
    (back : g.point w∈P) (inP : p∈P) (W : Line ℝ)
    (inj : Set.InjOn (affineEval W) (↑P : Set Point)) :
    ¬(∀ q∈P, affineEval W q≤affineEval W (g.point w)) := by
  intro max
  have coreY := previous_core G g dg w hw ho
  have onY := previous_on_line n L hL G g dg w ho i hc hp
  have yP := point_mem_closed G g dg w (w-2) hw coreY P closed back
  obtain ⟨t,ht,he⟩ := g.antipodal (w+1)
  have hi : (w+1)+3=w-2 := (by decide : ∀ w : ZMod 6, (w+1)+3=w-2) w
  simp only [Nat.cast_ofNat,hi] at he
  have areaY : areaDet (g.point w) (g.point (w+1)) (g.point (w-2))=
      (1+t)*areaDet (g.point w) (g.point (w+1)) g.center := by rw [he]; dsimp [areaDet]; ring
  have op : areaDet (g.point w) (g.point (w+1)) p*
      areaDet (g.point w) (g.point (w+1)) (g.point (w-2))<0 := by
    rw [areaY]
    have hprod := mul_neg_of_pos_of_neg (by linarith : 0<1+t) opposite
    nlinarith
  have col := UpperOpenMathN13Separated.area_zero_of_valid_line (L i) p (g.point w) (g.point (w-2))
    (line_valid n L hL hn i) pp hc onY
  have equal := collinear_max_equal (g.point w) (g.point (w+1)) p (g.point (w-2)) W col op
    (max p inP) (max _ yP)
  have eqp : p=g.point w := inj inP back equal
  rw [eqp] at opposite
  simp [areaDet] at opposite

theorem next_core_escape_not_max {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (G : α → TriangleGeometry) (g : Sectors n 3 L) (dg : AntipodalData G g)
    (w : ZMod 6) (hw : w∈g.coreShared) (ho : OrdinaryAt n L (g.point (w+1)))
    (i : Fin n) (p : Point)
    (hc : affineEval (L i) (g.point w)=0)
    (hp : affineEval (L i) (g.point (w+1))=0) (pp : affineEval (L i) p=0)
    (opposite : areaDet (g.point w) (g.point (w-1)) p*
      areaDet (g.point w) (g.point (w-1)) g.center<0)
    (P : Finset Point) (closed : SharedCoreClosed n L G P)
    (back : g.point w∈P) (inP : p∈P) (W : Line ℝ)
    (inj : Set.InjOn (affineEval W) (↑P : Set Point)) :
    ¬(∀ q∈P, affineEval W q≤affineEval W (g.point w)) := by
  intro max
  have coreY := next_core G g dg w hw ho
  have onY := next_on_line n L hL G g dg w ho i hc hp
  have yP := point_mem_closed G g dg w (w+2) hw coreY P closed back
  obtain ⟨t,ht,he⟩ := g.antipodal (w-1)
  have hi : (w-1)+3=w+2 := by ring
  simp only [Nat.cast_ofNat,hi] at he
  have areaY : areaDet (g.point w) (g.point (w-1)) (g.point (w+2))=
      (1+t)*areaDet (g.point w) (g.point (w-1)) g.center := by rw [he]; dsimp [areaDet]; ring
  have op : areaDet (g.point w) (g.point (w-1)) p*
      areaDet (g.point w) (g.point (w-1)) (g.point (w+2))<0 := by
    rw [areaY]
    have hprod := mul_neg_of_pos_of_neg (by linarith : 0<1+t) opposite
    nlinarith
  have col := UpperOpenMathN13Separated.area_zero_of_valid_line (L i) p (g.point w) (g.point (w+2))
    (line_valid n L hL hn i) pp hc onY
  have equal := collinear_max_equal (g.point w) (g.point (w-1)) p (g.point (w+2)) W col op
    (max p inP) (max _ yP)
  have eqp : p=g.point w := inj inP back equal
  rw [eqp] at opposite
  simp [areaDet] at opposite

theorem antipodal_back_not_both_core_neighbors {α : Type*} [Fintype α]
    {n : ℕ} {L : ℕ → Line ℝ} (G : α → TriangleGeometry)
    (g : Sectors n 3 L) (dg : AntipodalData G g) (w : ZMod 6)
    (hw : w∈g.coreShared)
    (prev : (supports n L (g.point (w-1))).card=3)
    (next : (supports n L (g.point (w+1))).card=3) : False := by
  classical
  have coreAt (z : ZMod 6) (card : (supports n L (g.point z)).card=3) : z∈g.coreShared := by
    apply mem_sdiff.mpr
    refine ⟨by simp [Sectors.shared,dg.triangular_eq],?_⟩
    intro ho
    have ord := ((g.mem_ordinaryShared z).mp ho).2.2
    have hc := (ordinary_iff_support_card n L (g.point z)).mp ord
    omega
  have hp := coreAt (w-1) prev
  have hn := coreAt (w+1) next
  have rule : ∀ w : ZMod 6, w∈({1,2,4,5} : Finset (ZMod 6)) →
      w-1∈({1,2,4,5} : Finset (ZMod 6)) → w+1∈({1,2,4,5} : Finset (ZMod 6)) → False := by decide
  rw [dg.core_eq] at hw hp hn
  exact rule w hw hp hn

theorem antipodal_core_pair_not_max {α : Type*} [Fintype α]
    {n : ℕ} {L : ℕ → Line ℝ} (G : α → TriangleGeometry)
    (f : Sectors n 3 L) (df : UpperOpenMathAntipodalFullNeighborPair.AnyChartData G f)
    (h0 : (0 : ZMod 6)∈f.coreShared) (h3 : (3 : ZMod 6)∈f.coreShared)
    (P : Finset Point) (closed : SharedCoreClosed n L G P) (center : f.center∈P)
    (W : Line ℝ) (inj : Set.InjOn (affineEval W) (↑P : Set Point)) :
    ¬(∀ q∈P, affineEval W q≤affineEval W f.center) := by
  classical
  intro max
  have edgeAt (z : ZMod 6) (hz : z∈f.coreShared) : ({f.center,f.point z} : Edge)∈twoCoreEdges n L G := by
    have he : ({f.center,f.point z} : Edge)∈f.coreShared.image (fun z=>({f.center,f.point z} : Edge)) :=
      mem_image.mpr ⟨z,hz,rfl⟩
    rw [df.core_image] at he
    exact (mem_filter.mp he).1
  have pP : f.point 0∈P := (closed _ (edgeAt 0 h0) f.center (by simp) center) (by simp)
  have qP : f.point 3∈P := (closed _ (edgeAt 3 h3) f.center (by simp) center) (by simp)
  obtain ⟨t,ht,he⟩ := f.antipodal 0
  simp only [zero_add,Nat.cast_ofNat] at he
  have hy : affineEval W (f.point 3)=(1+t)*affineEval W f.center-t*affineEval W (f.point 0) := by
    rw [he]; dsimp [affineEval]; ring
  have mp := max (f.point 0) pP
  have mq := max (f.point 3) qP
  have equal : affineEval W (f.point 0)=affineEval W f.center := by
    by_contra h
    have lt := lt_of_le_of_ne mp h
    have positive := mul_pos ht (sub_pos.mpr lt)
    rw [hy] at mq
    nlinarith
  exact df.noncentral 0 (inj pP center equal)

private theorem ordinary_after_previous_core {α : Type*} [Fintype α]
    {n : ℕ} {L : ℕ → Line ℝ} (G : α → TriangleGeometry)
    (g : Sectors n 3 L) (dg : AntipodalData G g) (w : ZMod 6)
    (hw : w∈g.coreShared) (prev : (supports n L (g.point (w-1))).card=3) :
    OrdinaryAt n L (g.point (w+1)) := by
  classical
  have hp : w-1∈g.coreShared := by
    apply mem_sdiff.mpr
    refine ⟨by simp [Sectors.shared,dg.triangular_eq],?_⟩
    intro h
    have card := (ordinary_iff_support_card n L _).mp (((g.mem_ordinaryShared _).mp h).2.2)
    omega
  have rule : ∀ w : ZMod 6, w∈({1,2,4,5} : Finset (ZMod 6)) →
      w-1∈({1,2,4,5} : Finset (ZMod 6)) → w+1∈({0,3} : Finset (ZMod 6)) := by decide
  have ho : w+1∈g.ordinaryShared := by
    rw [dg.ordinary_eq]
    rw [dg.core_eq] at hw hp
    exact rule w hw hp
  exact ((g.mem_ordinaryShared _).mp ho).2.2

private theorem ordinary_before_next_core {α : Type*} [Fintype α]
    {n : ℕ} {L : ℕ → Line ℝ} (G : α → TriangleGeometry)
    (g : Sectors n 3 L) (dg : AntipodalData G g) (w : ZMod 6)
    (hw : w∈g.coreShared) (next : (supports n L (g.point (w+1))).card=3) :
    OrdinaryAt n L (g.point (w-1)) := by
  classical
  have hp : w+1∈g.coreShared := by
    apply mem_sdiff.mpr
    refine ⟨by simp [Sectors.shared,dg.triangular_eq],?_⟩
    intro h
    have card := (ordinary_iff_support_card n L _).mp (((g.mem_ordinaryShared _).mp h).2.2)
    omega
  have rule : ∀ w : ZMod 6, w∈({1,2,4,5} : Finset (ZMod 6)) →
      w+1∈({1,2,4,5} : Finset (ZMod 6)) → w-1∈({0,3} : Finset (ZMod 6)) := by decide
  have ho : w-1∈g.ordinaryShared := by
    rw [dg.ordinary_eq]
    rw [dg.core_eq] at hw hp
    exact rule w hw hp
  exact ((g.mem_ordinaryShared _).mp ho).2.2

/-- An actual normalized N13 recipient touching an A0 star is not an
    injective-affine maximum in any finite closed shared-core set. -/
theorem certificate_n13_anti_not_max {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (triples : ∀ p∈core n L, (supports n L p).card=3)
    (f : Sectors n 3 L)
    (df : UpperOpenMathAntipodalFullNeighborPair.AnyChartData (fun a=>ofPredicate n L (tri a) hL (ht a)) f)
    (run : f.shared=({0,1,2,3} : Finset (ZMod 6))) (ac : f.ordinaryShared.card=1)
    (z : ZMod 6) (hz : z∈f.coreShared)
    (qa : f.point z∈unmarkedFullTwoCapSet n L hL hn tri ht)
    (P : Finset Point) (closed : SharedCoreClosed n L (fun a=>ofPredicate n L (tri a) hL (ht a)) P)
    (center : f.center∈P) (W : Line ℝ)
    (inj : Set.InjOn (affineEval W) (↑P : Set Point)) :
    ¬(∀ q∈P, affineEval W q≤affineEval W f.center) := by
  classical
  let G := fun a=>ofPredicate n L (tri a) hL (ht a)
  obtain ⟨o,ordEq⟩ := card_eq_one.mp ac
  have omem : o∈f.ordinaryShared := by rw [ordEq]; simp
  have ord : OrdinaryAt n L (f.point o) := ((f.mem_ordinaryShared o).mp omem).2.2
  have orun : o∈({0,1,2,3} : Finset (ZMod 6)) := by rw [←run]; exact f.ordinaryShared_subset omem
  have zrun : z∈({0,1,2,3} : Finset (ZMod 6)) := by rw [←run]; exact (mem_sdiff.mp hz).1
  have zne : z≠o := by intro he; subst z; exact (mem_sdiff.mp hz).2 omem
  have coreLab (a : ZMod 6) (ha : a∈({0,1,2,3} : Finset (ZMod 6))) (hao : a≠o) : a∈f.coreShared := by
    apply mem_sdiff.mpr
    refine ⟨by rw [run]; exact ha,?_⟩
    rw [ordEq]
    simpa using hao
  have rc (a : ZMod 6) (ha : a∈f.coreShared) : (supports n L (f.point a)).card=3 :=
    triples _ (UpperOpenMathN13ActualChart.certificate_chart_core_endpoint n L hL tri ht f df a ha)
  have inP (a : ZMod 6) (ha : a∈f.coreShared) : f.point a∈P := by
    have he : ({f.center,f.point a} : Edge)∈f.coreShared.image (fun a=>({f.center,f.point a} : Edge)) := mem_image.mpr ⟨a,ha,rfl⟩
    rw [df.core_image] at he
    exact (closed _ (mem_filter.mp he).1 f.center (by simp) center) (by simp)
  have flip (a b : Point) : areaDet f.center a b= -areaDet f.center b a := by dsimp [areaDet]; ring
  have cases : ∀ o z : ZMod 6, o∈({0,1,2,3} : Finset (ZMod 6)) →
      z∈({0,1,2,3} : Finset (ZMod 6)) → z≠o →
      (o=1∨o=2) ∨ (o=0∧(z=1∨z=2∨z=3)) ∨ (o=3∧(z=0∨z=1∨z=2)) := by decide
  obtain ⟨g,w,dg,gc,hw,gp,gr,gl⟩ := UpperOpenMathN13ActualChart.certificate_anti_neighbor_chart n L hL hn tri hi ht triples f df z hz qa
  rcases cases o z orun zrun zne with interior|⟨rfl,positions⟩|⟨rfl,positions⟩
  · rcases interior with rfl|rfl
    · exact antipodal_core_pair_not_max G f df (coreLab 0 (by decide) (by decide))
        (coreLab 3 (by decide) (by decide)) P closed center W inj
    · exact antipodal_core_pair_not_max G f df (coreLab 0 (by decide) (by decide))
        (coreLab 3 (by decide) (by decide)) P closed center W inj
  · rcases positions with rfl|rfl|rfl
    · have ho : OrdinaryAt n L (g.point (w+1)) := by rw [gl]; exact ord
      have op : areaDet (g.point w) (g.point (w-1)) (f.point 3)*areaDet (g.point w) (g.point (w-1)) g.center<0 := by
        rw [gp,gr,gc]
        change areaDet f.center (f.point 2) (f.point 3)*areaDet f.center (f.point 2) (f.point 1)<0
        rw [flip (f.point 2) (f.point 1)]
        exact mul_neg_of_pos_of_neg (df.positive 2) (neg_neg_of_pos (df.positive 1))
      have escape := next_core_escape_not_max n L hL hn G g dg w hw ho (f.radial 0) (f.point 3)
        (by rw [gp]; exact f.radial_center 0) (by rw [gl]; exact f.radial_point 0)
        (by exact antipodal_line_point f (L (f.radial 0)) 0 (f.radial_center 0) (f.radial_point 0))
        op P closed (by rw [gp]; exact center) (inP 3 (coreLab 3 (by decide) (by decide))) W inj
      simpa only [gp] using escape
    · exact False.elim (antipodal_back_not_both_core_neighbors G g dg w hw
        (by rw [gr]; exact rc 3 (coreLab 3 (by decide) (by decide)))
        (by rw [gl]; exact rc 1 (coreLab 1 (by decide) (by decide))))
    · have ho := ordinary_before_next_core G g dg w hw
        (by rw [gl]; exact rc 2 (coreLab 2 (by decide) (by decide)))
      have op : areaDet (g.point w) (g.point (w+1)) (f.point 1)*areaDet (g.point w) (g.point (w+1)) g.center<0 := by
        rw [gp,gl,gc]
        change areaDet f.center (f.point 2) (f.point 1)*areaDet f.center (f.point 2) (f.point 3)<0
        rw [flip (f.point 2) (f.point 1)]
        exact mul_neg_of_neg_of_pos (neg_neg_of_pos (df.positive 1)) (df.positive 2)
      have escape := previous_core_escape_not_max n L hL hn G g dg w hw ho (f.radial 1) (f.point 1)
        (by rw [gp]; exact f.radial_center 1)
        (by rw [gr]; exact antipodal_line_point f (L (f.radial 1)) 1 (f.radial_center 1) (f.radial_point 1))
        (f.radial_point 1) op P closed (by rw [gp]; exact center)
        (inP 1 (coreLab 1 (by decide) (by decide))) W inj
      simpa only [gp] using escape
  · rcases positions with rfl|rfl|rfl
    · have ho := ordinary_after_previous_core G g dg w hw
        (by rw [gr]; exact rc 1 (coreLab 1 (by decide) (by decide)))
      have op : areaDet (g.point w) (g.point (w-1)) (f.point 2)*areaDet (g.point w) (g.point (w-1)) g.center<0 := by
        rw [gp,gr,gc]
        change areaDet f.center (f.point 1) (f.point 2)*areaDet f.center (f.point 1) (f.point 0)<0
        rw [flip (f.point 1) (f.point 0)]
        exact mul_neg_of_pos_of_neg (df.positive 1) (neg_neg_of_pos (df.positive 0))
      have escape := next_core_escape_not_max n L hL hn G g dg w hw ho (f.radial 2) (f.point 2)
        (by rw [gp]; exact f.radial_center 2)
        (by rw [gl]; exact antipodal_line_point f (L (f.radial 2)) 2 (f.radial_center 2) (f.radial_point 2))
        (f.radial_point 2) op P closed (by rw [gp]; exact center)
        (inP 2 (coreLab 2 (by decide) (by decide))) W inj
      simpa only [gp] using escape
    · exact False.elim (antipodal_back_not_both_core_neighbors G g dg w hw
        (by rw [gr]; exact rc 2 (coreLab 2 (by decide) (by decide)))
        (by rw [gl]; exact rc 0 (coreLab 0 (by decide) (by decide))))
    · have ho : OrdinaryAt n L (g.point (w-1)) := by rw [gr]; exact ord
      have op : areaDet (g.point w) (g.point (w+1)) (f.point 0)*areaDet (g.point w) (g.point (w+1)) g.center<0 := by
        rw [gp,gl,gc]
        change areaDet f.center (f.point 1) (f.point 0)*areaDet f.center (f.point 1) (f.point 2)<0
        rw [flip (f.point 1) (f.point 0)]
        exact mul_neg_of_neg_of_pos (neg_neg_of_pos (df.positive 0)) (df.positive 1)
      have escape := previous_core_escape_not_max n L hL hn G g dg w hw ho (f.radial 0) (f.point 0)
        (by rw [gp]; exact f.radial_center 0)
        (by rw [gr]; exact antipodal_line_point f (L (f.radial 0)) 0 (f.radial_center 0) (f.radial_point 0))
        (f.radial_point 0) op P closed (by rw [gp]; exact center)
        (inP 0 (coreLab 0 (by decide) (by decide))) W inj
      simpa only [gp] using escape

#print axioms certificate_n13_anti_not_max
#print axioms antipodal_back_not_both_core_neighbors
#print axioms antipodal_core_pair_not_max
#print axioms previous_core_escape_not_max
#print axioms next_core_escape_not_max
end Kobon.UpperOpenMathN13SupportExtreme



