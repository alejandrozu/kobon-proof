import Kobon.UpperCleanEdges
import Kobon.UpperCleanPairing
import Kobon.UpperFanSupport

/-!
# Triangle bases at a clean line

This module builds the geometric maps used in the clean-line pairing proof.
-/
namespace Kobon.UpperCleanCover
open Cells FanGeometry UpperVertexBudget UpperTriangleIncidence
  UpperSharedIncidence UpperEdgeInventory UpperCleanHalfplane
  UpperCleanEdges UpperCleanPairing Finset

def value (cut : Line ℝ) (t : TriangleGeometry) : ℝ :=
  affineEval cut t.p+affineEval cut t.q+affineEval cut t.r

def SameSides (s t : TriangleGeometry) : Prop :=
  ∀ i : Fin 3, ∃ j : Fin 3, edge s i=edge t j

theorem sameSides_refl (t : TriangleGeometry) : SameSides t t := fun i => ⟨i,rfl⟩

theorem SameSides.trans {s t u : TriangleGeometry}
    (hst : SameSides s t) (htu : SameSides t u) : SameSides s u := by
  intro i
  obtain ⟨j,hj⟩ := hst i
  obtain ⟨k,hk⟩ := htu j
  exact ⟨k,hj.trans hk⟩

theorem cycle_sides (t : TriangleGeometry) : SameSides (cycle t) t := by
  intro i
  fin_cases i
  · exact ⟨1,rfl⟩
  · exact ⟨2,rfl⟩
  · exact ⟨0,rfl⟩

theorem swap_sides (t : TriangleGeometry) : SameSides (swap t) t := by
  intro i
  fin_cases i
  · refine ⟨0,?_⟩
    change {t.q,t.p}={t.p,t.q}
    exact pair_comm _ _
  · refine ⟨2,?_⟩
    change {t.p,t.r}={t.r,t.p}
    exact pair_comm _ _
  · refine ⟨1,?_⟩
    change {t.r,t.q}={t.q,t.r}
    exact pair_comm _ _

theorem sideTriangle_sides (t : TriangleGeometry) (i : Fin 3) :
    SameSides (sideTriangle t i) t := by
  fin_cases i
  · exact sameSides_refl t
  · exact cycle_sides t
  · exact (cycle_sides (cycle t)).trans (cycle_sides t)

@[simp] theorem value_cycle (cut : Line ℝ) (t : TriangleGeometry) :
    value cut (cycle t)=value cut t := by dsimp [value,cycle]; ring

@[simp] theorem value_swap (cut : Line ℝ) (t : TriangleGeometry) :
    value cut (swap t)=value cut t := by dsimp [value,swap]; ring

@[simp] theorem value_sideTriangle (cut : Line ℝ) (t : TriangleGeometry) (i : Fin 3) :
    value cut (sideTriangle t i)=value cut t := by fin_cases i <;> simp [sideTriangle]

/-- Align a real side while retaining all actual original sides and the
sum of affine vertex evaluations. -/
theorem align_with_sides {n : ℕ} {L : ℕ → Line ℝ}
    (t : TriangleGeometry) (ht : Indexed n L t) (i : Fin 3)
    (p q : Point) (he : edge t i={p,q}) (cut : Line ℝ) :
    ∃ s : TriangleGeometry, s.p=p ∧ s.q=q ∧ Indexed n L s ∧
      SameSides s t ∧ value cut s=value cut t := by
  classical
  let s := sideTriangle t i
  have hs : Indexed n L s := sideTriangle_indexed ht i
  have hsp : s.p=p ∨ s.p=q := by
    have h : s.p∈edge t i := by simp [edge,s]
    simpa only [he,mem_insert,mem_singleton] using h
  have hsq : s.q=p ∨ s.q=q := by
    have h : s.q∈edge t i := by simp [edge,s]
    simpa only [he,mem_insert,mem_singleton] using h
  have hne := nondegenerate_pair_ne s.p s.q s.r s.nondegenerate
  rcases hsp with hsp|hsp <;> rcases hsq with hsq|hsq
  · exact False.elim (hne (hsp.trans hsq.symm))
  · exact ⟨s,hsp,hsq,hs,sideTriangle_sides t i,value_sideTriangle cut t i⟩
  · exact ⟨swap s,hsq,hsp,swap_indexed hs,
      (swap_sides s).trans (sideTriangle_sides t i),by simp [s]⟩
  · exact False.elim (hne (hsp.trans hsq.symm))

def OnCut (cut : Line ℝ) (e : Edge) : Prop := ∀ p∈e, affineEval cut p=0

theorem side_on_cut_unique (cut : Line ℝ) (hv : cut.a≠0 ∨ cut.b≠0)
    (t : TriangleGeometry) (i j : Fin 3)
    (hi : OnCut cut (edge t i)) (hj : OnCut cut (edge t j)) : i=j := by
  classical
  by_contra hne
  have hz : affineEval cut t.p=0 ∧ affineEval cut t.q=0 ∧ affineEval cut t.r=0 := by
    fin_cases i <;> fin_cases j
    all_goals first | exact False.elim (hne rfl) |
      (simp only [OnCut,edge,sideTriangle,cycle,Fin.reduceFinMk,ite_true,ite_false,
        mem_insert,mem_singleton] at hi hj; aesop)
  obtain ⟨ha,hb⟩ := three_zeros_force_zero_normal cut t.p t.q t.r
    t.nondegenerate hz.1 hz.2.1 hz.2.2
  exact hv.elim (fun h => h ha) (fun h => h hb)

/-- Any actual inventory edge lying on a specified indexed line belongs
to that line's own consecutive inventory. -/
theorem inventory_on_support
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (i : Fin n) (e : Edge) (he : e∈edges n L)
    (hon : ∀ p∈e, affineEval (L i) p=0) : e∈lineEdges n L i := by
  classical
  obtain ⟨j,hj,hej⟩ := mem_biUnion.mp he
  by_cases hji : j=i
  · simpa only [hji] using hej
  · obtain ⟨k,hk,hke⟩ := mem_image.mp hej
    have hcard : e.card=2 := by rw [← hke]; exact intervalEdge_card n L j k
    obtain ⟨p,q,hpq,hepq⟩ := card_eq_two.mp hcard
    have hp : p∈e := by simp [hepq]
    have hq : q∈e := by simp [hepq]
    exact False.elim (hpq (two_lines_two_points (L j) (L i) p q
      (noParallel_any n L hL j i j.isLt i.isLt (fun h => hji (Fin.ext h)))
      (edge_endpoints_on_line n L hL hn hej p hp)
      (edge_endpoints_on_line n L hL hn hej q hq) (hon p hp) (hon q hq)))

theorem inventory_vertex
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (i : Fin n) {e : Edge} (he : e∈lineEdges n L i) {p : Point} (hp : p∈e) :
    p∈onLine n L i := by
  classical
  obtain ⟨k,hk,rfl⟩ := mem_image.mp he
  simp only [intervalEdge,mem_insert,mem_singleton] at hp
  rcases hp with rfl|rfl <;> exact orderedPoint_mem n L hL hn i _

theorem base_at_point {n : ℕ} {L : ℕ → Line ℝ}
    (cut : Line ℝ) (t : TriangleGeometry) (ht : Indexed n L t)
    (i : Fin 3) (hon : OnCut cut (edge t i)) (hval : 0<value cut t)
    (p : Point) (hp : p∈edge t i) :
    ∃ s : TriangleGeometry, s.p=p ∧ affineEval cut s.q=0 ∧
      0<affineEval cut s.r ∧ Indexed n L s ∧ SameSides s t := by
  classical
  let s := sideTriangle t i
  have hsp : affineEval cut s.p=0 := hon _ (by simp [edge,s])
  have hsq : affineEval cut s.q=0 := hon _ (by simp [edge,s])
  have hsr : 0<affineEval cut s.r := by
    have hh : 0<value cut s := by simpa [s] using hval
    dsimp [value] at hh
    linarith
  have hpp : p=s.p ∨ p=s.q := by simpa only [edge,mem_insert,mem_singleton] using hp
  rcases hpp with hpp|hpp
  · exact ⟨s,hpp.symm,hsq,hsr,sideTriangle_indexed ht i,sideTriangle_sides t i⟩
  · exact ⟨swap s,hpp.symm,hsp,hsr,swap_indexed (sideTriangle_indexed ht i),
      (swap_sides s).trans (sideTriangle_sides t i)⟩

/-- A positive-side triangle base through a clean crossing has an actual
side equal to the selected positive transverse segment at that crossing. -/
theorem base_selected_side {n : ℕ} {L : ℕ → Line ℝ}
    (hL : NoParallel n L) (hn : 2≤n) (line radial : Fin n)
    (cut : Line ℝ) (hcut : ∀ p, affineEval cut p=0 ↔ affineEval (L line) p=0)
    (p tip : Point) (hp : p∈onLine n L line) (ho : OrdinaryAt n L p)
    (hrad : radial≠line) (hprad : affineEval (L radial) p=0)
    (hsel : {p,tip}∈lineEdges n L radial) (hpos : 0<affineEval cut tip)
    (t : TriangleGeometry) (ht : Indexed n L t)
    (hsides : ∀ i, edge t i∈edges n L)
    (i : Fin 3) (hon : OnCut cut (edge t i))
    (hval : 0<value cut t) (hpe : p∈edge t i) :
    ∃ j : Fin 3, edge t j={p,tip} := by
  classical
  obtain ⟨s,hsp,hsq,hsr,hindex,hside⟩ := base_at_point cut t ht i hon hval p hpe
  obtain ⟨a,b,c,ha,hb,hc⟩ := hindex
  have hpb : affineEval (L b) p=0 := by simpa only [hb,hsp] using s.Bp
  have hbr : affineEval (L b) s.r=0 := by simpa only [hb] using s.Br
  have hbl : b≠line := by
    intro he
    rw [he] at hbr
    have hz := (hcut s.r).mpr hbr
    linarith
  have hrb : radial=b := ordinary_nonradial_unique n L p ho line radial b
    (mem_filter.mp hp).2 hprad hpb hrad hbl
  obtain ⟨j,hj⟩ := hside 2
  have hjpair : edge t j={p,s.r} := by
    rw [← hj]
    change {s.r,s.p}={p,s.r}
    rw [hsp,pair_comm]
  have hrEdge : {p,s.r}∈lineEdges n L radial := by
    apply inventory_on_support n L hL hn radial {p,s.r}
    · rw [← hjpair]
      exact hsides j
    · intro x hx
      simp only [mem_insert,mem_singleton] at hx
      rcases hx with rfl|rfl
      · exact hprad
      · simpa only [hrb] using hbr
  have hpr : p∈onLine n L radial := mem_filter.mpr ⟨(mem_filter.mp hp).1,hprad⟩
  have hrmem : s.r∈onLine n L radial := inventory_vertex n L hL hn radial hrEdge (by simp)
  have htipmem : tip∈onLine n L radial := inventory_vertex n L hL hn radial hsel (by simp)
  have heq : s.r=tip := incident_positive_unique n L hL hn radial cut p s.r tip
    hpr hrmem htipmem hrEdge hsel ((hcut p).mpr (mem_filter.mp hp).2) hsr hpos
  exact ⟨j,by simpa only [heq] using hjpair⟩

section Cover
variable {α : Type*} [Fintype α]

noncomputable def bases (cut : Line ℝ) (t : α → TriangleGeometry) : Finset Edge := by
  classical
  exact (univ.filter (fun a : α × Fin 3 => OnCut cut (sideMap t a) ∧
    0<value cut (t a.1))).image (sideMap t)

/-- Actual degree-one selected segments force a disjoint two-element cover
by actual triangle bases. All supports, segment membership and degrees refer
to real geometry; a pairing is not supplied as a premise. -/
theorem actual_base_cover
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (line : Fin n) (hc : Clean n L line)
    (cut : Line ℝ) (hcut : ∀ p, affineEval cut p=0 ↔ affineEval (L line) p=0)
    (hvalid : cut.a≠0 ∨ cut.b≠0)
    (t : α → TriangleGeometry) (ht : ∀ a, Indexed n L (t a))
    (hsides : ∀ a i, edge (t a) i∈edges n L)
    (radial : Point → Fin n) (tip : Point → Point)
    (hrad : ∀ p∈onLine n L line, radial p≠line)
    (hprad : ∀ p∈onLine n L line, affineEval (L (radial p)) p=0)
    (hsel : ∀ p∈onLine n L line, {p,tip p}∈lineEdges n L (radial p))
    (hpos : ∀ p∈onLine n L line, 0<affineEval cut (tip p))
    (hdegree : ∀ p∈onLine n L line, degree t {p,tip p}=1) :
    (∀ e∈bases cut t, e.card=2) ∧
    ((bases cut t : Set Edge).PairwiseDisjoint id) ∧
    (bases cut t).biUnion id=onLine n L line := by
  classical
  have hsub : ∀ e∈bases cut t, e⊆onLine n L line := by
    intro e he
    obtain ⟨⟨a,i⟩,hai,rfl⟩ := mem_image.mp he
    have hb := (mem_filter.mp hai).2
    have heline := inventory_on_support n L hL hn line (sideMap t (a,i)) (hsides a i)
      (fun p hp => (hcut p).mp (hb.1 p hp))
    intro p hp
    exact inventory_vertex n L hL hn line heline hp
  have hcover : ∀ p∈onLine n L line, ∃ e∈bases cut t, p∈e := by
    intro p hp
    have hd := hdegree p hp
    obtain ⟨x,hx⟩ := card_pos.mp (show 0<(univ.filter (fun x : α × Fin 3 => sideMap t x={p,tip p})).card by
      change 0<degree t {p,tip p}; omega)
    have hxe := (mem_filter.mp hx).2
    obtain ⟨s,hsp,hsq,hindex,hside,hvalue⟩ := align_with_sides (t x.1) (ht x.1) x.2 p (tip p) hxe cut
    have hpzero : affineEval cut s.p=0 := by simpa only [hsp] using (hcut p).mpr (mem_filter.mp hp).2
    have hqpos : 0<affineEval cut s.q := by simpa only [hsq] using hpos p hp
    have hrzero : affineEval cut s.r=0 := by
      have ho : OrdinaryAt n L s.p := by simpa only [hsp] using hc p hp
      rcases ordinary_vertex_pairs_on_line n L line s hindex ho ((hcut s.p).mp hpzero) with hh|hh
      · have hz := (hcut s.q).mpr hh.1; linarith
      · exact (hcut s.r).mpr hh.1
    obtain ⟨j,hj⟩ := hside 2
    have hbase : OnCut cut (edge (t x.1) j) := by
      rw [← hj]
      intro v hv
      change v∈{s.r,s.p} at hv
      simp only [mem_insert,mem_singleton] at hv
      rcases hv with rfl|rfl <;> assumption
    have hval : 0<value cut (t x.1) := by
      rw [← hvalue]
      dsimp [value]
      linarith
    refine ⟨edge (t x.1) j,mem_image.mpr ⟨(x.1,j),mem_filter.mpr
      ⟨mem_univ _,hbase,hval⟩,rfl⟩,?_⟩
    rw [← hj]
    change p∈{s.r,s.p}
    simp [hsp]
  have hdisj : (bases cut t : Set Edge).PairwiseDisjoint id := by
    intro e he f hf hef
    apply disjoint_left.mpr
    intro p hpe hpf
    have hp := hsub e he hpe
    obtain ⟨⟨a,i⟩,hai,hae⟩ := mem_image.mp he
    obtain ⟨⟨b,j⟩,hbj,hbf⟩ := mem_image.mp hf
    change edge (t a) i=e at hae
    change edge (t b) j=f at hbf
    have ha := (mem_filter.mp hai).2
    have hb := (mem_filter.mp hbj).2
    have hpa : p∈edge (t a) i := by rw [hae]; exact hpe
    have hpb : p∈edge (t b) j := by rw [hbf]; exact hpf
    obtain ⟨u,hu⟩ := base_selected_side hL hn line (radial p) cut hcut p (tip p) hp (hc p hp)
      (hrad p hp) (hprad p hp) (hsel p hp) (hpos p hp) (t a) (ht a) (hsides a) i ha.1 ha.2 hpa
    obtain ⟨v,hv⟩ := base_selected_side hL hn line (radial p) cut hcut p (tip p) hp (hc p hp)
      (hrad p hp) (hprad p hp) (hsel p hp) (hpos p hp) (t b) (ht b) (hsides b) j hb.1 hb.2 hpb
    obtain ⟨w,hw⟩ := card_eq_one.mp (hdegree p hp)
    have hau : (a,u)∈univ.filter (fun z : α × Fin 3 => sideMap t z={p,tip p}) :=
      mem_filter.mpr ⟨mem_univ _,hu⟩
    have hbv : (b,v)∈univ.filter (fun z : α × Fin 3 => sideMap t z={p,tip p}) :=
      mem_filter.mpr ⟨mem_univ _,hv⟩
    rw [hw] at hau hbv
    have hab : a=b := congrArg Prod.fst ((mem_singleton.mp hau).trans (mem_singleton.mp hbv).symm)
    subst b
    have hij := side_on_cut_unique cut hvalid (t a) i j ha.1 hb.1
    apply hef
    exact hae.symm.trans ((congrArg (edge (t a)) hij).trans hbf)
  refine ⟨?_,hdisj,?_⟩
  · intro e he
    obtain ⟨⟨a,i⟩,hai,rfl⟩ := mem_image.mp he
    exact edge_card (t a) i
  · ext p
    constructor
    · intro hp
      obtain ⟨e,he,hpe⟩ := mem_biUnion.mp hp
      exact hsub e he hpe
    · intro hp
      obtain ⟨e,he,hpe⟩ := hcover p hp
      exact mem_biUnion.mpr ⟨e,he,hpe⟩

theorem selected_degree_not_all_one
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (line : Fin n) (hc : Clean n L line) (heven : n%2=0)
    (cut : Line ℝ) (hcut : ∀ p, affineEval cut p=0 ↔ affineEval (L line) p=0)
    (hvalid : cut.a≠0 ∨ cut.b≠0)
    (t : α → TriangleGeometry) (ht : ∀ a, Indexed n L (t a))
    (hsides : ∀ a i, edge (t a) i∈edges n L)
    (radial : Point → Fin n) (tip : Point → Point)
    (hrad : ∀ p∈onLine n L line, radial p≠line)
    (hprad : ∀ p∈onLine n L line, affineEval (L (radial p)) p=0)
    (hsel : ∀ p∈onLine n L line, {p,tip p}∈lineEdges n L (radial p))
    (hpos : ∀ p∈onLine n L line, 0<affineEval cut (tip p)) :
    ∃ p∈onLine n L line, degree t {p,tip p}≠1 := by
  classical
  by_contra h
  push Not at h
  obtain ⟨hcard,hdisj,hcover⟩ := actual_base_cover n L hL hn line hc cut hcut hvalid t ht hsides radial tip
    hrad hprad hsel hpos h
  exact clean_line_no_pair_partition n L hL line hc heven (bases cut t) hcard hdisj hcover

theorem common_positive_cut
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 3≤n)
    (line : Fin n) (hc : Clean n L line) :
    ∃ cut : Line ℝ, (cut.a≠0 ∨ cut.b≠0) ∧
      (∀ p, affineEval cut p=0 ↔ affineEval (L line) p=0) ∧
      ∀ i : Fin n, i≠line → ∃ q : Point,
        {intersection (L line) (L i),q}∈lineEdges n L i ∧ 0<affineEval cut q := by
  rcases common_bounded_side n L hL hn line hc with hpos|hneg
  · exact ⟨L line,line_valid n L hL (by omega) line,fun _ => Iff.rfl,hpos⟩
  · let cut : Line ℝ := ⟨-(L line).a,-(L line).b,-(L line).c⟩
    have he : ∀ p, affineEval cut p= -affineEval (L line) p := by
      intro p
      dsimp [cut,affineEval]
      ring
    refine ⟨cut,?_,?_,?_⟩
    · rcases line_valid n L hL (by omega) line with ha|hb
      · exact Or.inl (neg_ne_zero.mpr ha)
      · exact Or.inr (neg_ne_zero.mpr hb)
    · intro p
      rw [he,neg_eq_zero]
    · intro i hi
      obtain ⟨q,hq,hneg⟩ := hneg i hi
      exact ⟨q,hq,by rw [he]; linarith⟩

/-- A clean line in an even-order arrangement has an actual transverse
consecutive segment whose degree in the supplied triangle family is not one.
All selected segments, their common side and the pairing are extracted here. -/
theorem clean_line_bad_degree
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 3≤n)
    (line : Fin n) (hc : Clean n L line) (heven : n%2=0)
    (t : α → TriangleGeometry) (ht : ∀ a, Indexed n L (t a))
    (hsides : ∀ a i, edge (t a) i∈edges n L) :
    ∃ p∈onLine n L line, ∃ radial : Fin n, radial≠line ∧
      affineEval (L radial) p=0 ∧ ∃ q : Point,
      {p,q}∈lineEdges n L radial ∧ degree t {p,q}≠1 := by
  classical
  obtain ⟨cut,hvalid,hcut,hside⟩ := common_positive_cut n L hL hn line hc
  have hcross : ∀ p∈onLine n L line, ∃ i : Fin n,
      i≠line ∧ intersection (L line) (L i)=p := by
    intro p hp
    rw [← crossings_image n L hL line] at hp
    obtain ⟨i,hi,he⟩ := mem_image.mp hp
    exact ⟨i,(mem_erase.mp hi).1,he⟩
  have hradchoice : ∀ p : Point, ∃ i : Fin n, p∈onLine n L line →
      i≠line ∧ intersection (L line) (L i)=p := by
    intro p
    by_cases hp : p∈onLine n L line
    · obtain ⟨i,hi,he⟩ := hcross p hp
      exact ⟨i,fun _ => ⟨hi,he⟩⟩
    · exact ⟨line,fun hh => False.elim (hp hh)⟩
  choose radial hrad using hradchoice
  have htipchoice : ∀ p : Point, ∃ q : Point, p∈onLine n L line →
      {p,q}∈lineEdges n L (radial p) ∧ 0<affineEval cut q := by
    intro p
    by_cases hp : p∈onLine n L line
    · obtain ⟨q,hq,hpos⟩ := hside (radial p) (hrad p hp).1
      rw [(hrad p hp).2] at hq
      exact ⟨q,fun _ => ⟨hq,hpos⟩⟩
    · exact ⟨p,fun hh => False.elim (hp hh)⟩
  choose tip htip using htipchoice
  have hprad : ∀ p∈onLine n L line, affineEval (L (radial p)) p=0 := by
    intro p hp
    have hh := intersection_on_right _ _ (noParallel_any n L hL line (radial p)
      line.isLt (radial p).isLt (fun h => (hrad p hp).1 (Fin.ext h).symm))
    simpa only [(hrad p hp).2] using hh
  obtain ⟨p,hp,hbad⟩ := selected_degree_not_all_one n L hL (by omega) line hc heven
    cut hcut hvalid t ht hsides radial tip (fun p hp => (hrad p hp).1) hprad
    (fun p hp => (htip p hp).1) (fun p hp => (htip p hp).2)
  exact ⟨p,hp,radial p,(hrad p hp).1,hprad p hp,tip p,(htip p hp).1,hbad⟩

/-- Fully geometric local clean-line charging conclusion for a finite
injective certified triangle family: an unused or D1 edge has an ordinary
endpoint on the clean line and a different supporting line. -/
theorem certificate_clean_line_charge
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 3≤n)
    (line : Fin n) (hc : Clean n L line) (heven : n%2=0)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a)) :
    let t := fun a => ofPredicate n L (tri a) hL (ht a)
    ∃ e : Edge, (e∈edges n L\usedEdges t ∨ e∈oneCoreEdges n L t) ∧
      ∃ p∈e, p∈onLine n L line ∧ ∃ radial : Fin n,
        radial≠line ∧ e∈lineEdges n L radial := by
  classical
  let t := fun a => ofPredicate n L (tri a) hL (ht a)
  have hindex : ∀ a, Indexed n L (t a) := fun a => predicate_indexed n L (tri a) hL (ht a)
  have hsides : ∀ a i, edge (t a) i∈edges n L :=
    fun a i => predicate_side_mem_edges n L hL (by omega) (tri a) (ht a) i
  obtain ⟨p,hp,radial,hrad,hprad,q,he,hbad⟩ := clean_line_bad_degree n L hL hn line hc heven t hindex hsides
  have hglobal : {p,q}∈edges n L := mem_biUnion.mpr ⟨radial,mem_univ _,he⟩
  have hd : Pairwise (fun a b => Disjoint (t a).interior (t b).interior) := by
    intro a b hab
    exact distinct_interiors_disjoint n L _ _ hL (ht a) (ht b) (fun h => hab (hi h))
  refine ⟨{p,q},?_,p,by simp,hp,radial,hrad,he⟩
  by_cases hu : {p,q}∈usedEdges t
  · right
    have hdeg := degree_pos t hu
    have hmax := degree_le_two t hd {p,q}
    have htwo : degree t {p,q}=2 := by omega
    exact mem_filter.mpr ⟨mem_filter.mpr ⟨hu,htwo⟩,p,by simp,hc p hp⟩
  · exact Or.inl (mem_sdiff.mpr ⟨hglobal,hu⟩)
end Cover

#print axioms align_with_sides
#print axioms side_on_cut_unique
#print axioms inventory_on_support
#print axioms base_selected_side
#print axioms actual_base_cover
#print axioms selected_degree_not_all_one
#print axioms clean_line_bad_degree
#print axioms certificate_clean_line_charge
end Kobon.UpperCleanCover
