import Kobon.UpperOpenMathOrdinaryCutParity
import Kobon.UpperCleanCover

/-!
# Actual positive triangle bases at ordinary crossings of any cutting line

A core line cannot use the clean-line pairing argument verbatim. A triangle
base can cover one ordinary crossing and one core. Once those bases are
excluded, the actual positive bases touching ordinary crossings form a
disjoint pair partition of the odd ordinary crossing set. The obstruction
below records the additional core-ended-base outcome explicitly.
-/
namespace Kobon.UpperOpenMathOrdinaryBaseCover
open Cells FanGeometry UpperVertexBudget UpperTriangleIncidence UpperSharedIncidence
  UpperEdgeInventory UpperCoreExtraction UpperCleanCover UpperOpenMathOrdinaryCutParity Finset
open UpperCleanEdges UpperCleanHalfplane

noncomputable def touchingBases {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (cut : Line ℝ) (t : α → TriangleGeometry) : Finset Edge := by
  classical
  exact (bases cut t).filter (fun e => ∃ p∈e, OrdinaryAt n L p)

theorem actual_ordinary_base_cover {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n) (line : Fin n)
    (cut : Line ℝ) (hcut : ∀ p, affineEval cut p=0 ↔ affineEval (L line) p=0)
    (hvalid : cut.a≠0 ∨ cut.b≠0)
    (t : α → TriangleGeometry) (ht : ∀ a, Indexed n L (t a))
    (hsides : ∀ a i, edge (t a) i∈edges n L)
    (radial : Point → Fin n) (tip : Point → Point)
    (hrad : ∀ p∈ordinaryOnLine n L line, radial p≠line)
    (hprad : ∀ p∈ordinaryOnLine n L line, affineEval (L (radial p)) p=0)
    (hsel : ∀ p∈ordinaryOnLine n L line, {p,tip p}∈lineEdges n L (radial p))
    (hpos : ∀ p∈ordinaryOnLine n L line, 0<affineEval cut (tip p))
    (hdegree : ∀ p∈ordinaryOnLine n L line, degree t {p,tip p}=1)
    (hordinary : ∀ e∈touchingBases n L cut t, ∀ p∈e, OrdinaryAt n L p) :
    (∀ e∈touchingBases n L cut t, e.card=2) ∧
    ((touchingBases n L cut t : Set Edge).PairwiseDisjoint id) ∧
    (touchingBases n L cut t).biUnion id=ordinaryOnLine n L line := by
  classical
  have hsub : ∀ e∈touchingBases n L cut t, e⊆ordinaryOnLine n L line := by
    intro e he p hp
    have heBase := (mem_filter.mp he).1
    obtain ⟨⟨a,i⟩,hai,heq⟩ := mem_image.mp heBase
    have hb := (mem_filter.mp hai).2
    have heInv : e∈edges n L := by simpa only [← heq,sideMap] using hsides a i
    have heLine := inventory_on_support n L hL hn line e heInv
      (fun q hq => (hcut q).mp (hb.1 q (by simpa only [heq] using hq)))
    exact mem_filter.mpr ⟨inventory_vertex n L hL hn line heLine hp,hordinary e he p hp⟩
  have hcover : ∀ p∈ordinaryOnLine n L line, ∃ e∈touchingBases n L cut t, p∈e := by
    intro p hp
    have hpLine := (mem_filter.mp hp).1
    have hpOrd := (mem_filter.mp hp).2
    have hd := hdegree p hp
    obtain ⟨x,hx⟩ := card_pos.mp (show 0<(univ.filter (fun x : α × Fin 3 => sideMap t x={p,tip p})).card by
      change 0<degree t {p,tip p}; omega)
    have hxe := (mem_filter.mp hx).2
    obtain ⟨s,hsp,hsq,hindex,hside,hvalue⟩ := align_with_sides (t x.1) (ht x.1) x.2 p (tip p) hxe cut
    have hpzero : affineEval cut s.p=0 := by simpa only [hsp] using (hcut p).mpr (mem_filter.mp hpLine).2
    have hqpos : 0<affineEval cut s.q := by simpa only [hsq] using hpos p hp
    have hrzero : affineEval cut s.r=0 := by
      have ho : OrdinaryAt n L s.p := by simpa only [hsp] using hpOrd
      rcases ordinary_vertex_pairs_on_line n L line s hindex ho ((hcut s.p).mp hpzero) with hh|hh
      · have hz := (hcut s.q).mpr hh.1; linarith
      · exact (hcut s.r).mpr hh.1
    obtain ⟨j,hj⟩ := hside 2
    have hbase : OnCut cut (edge (t x.1) j) := by
      rw [← hj]
      intro v hv
      change v∈{s.r,s.p} at hv
      rcases mem_insert.mp hv with hv|hv
      · simpa only [hv] using hrzero
      · simpa only [mem_singleton.mp hv] using hpzero
    have hval : 0<value cut (t x.1) := by
      rw [← hvalue]
      dsimp [value]
      linarith
    have hpBase : p∈edge (t x.1) j := by
      rw [← hj]
      change p∈{s.r,s.p}
      simp [hsp]
    refine ⟨edge (t x.1) j,mem_filter.mpr ⟨?_,⟨p,hpBase,hpOrd⟩⟩,hpBase⟩
    exact mem_image.mpr ⟨(x.1,j),mem_filter.mpr ⟨mem_univ _,hbase,hval⟩,rfl⟩
  have hdisj : (touchingBases n L cut t : Set Edge).PairwiseDisjoint id := by
    intro e he f hf hef
    apply disjoint_left.mpr
    intro p hpe hpf
    have hp := hsub e he hpe
    have hpLine := (mem_filter.mp hp).1
    have hpOrd := (mem_filter.mp hp).2
    obtain ⟨⟨a,i⟩,hai,hae⟩ := mem_image.mp (mem_filter.mp he).1
    obtain ⟨⟨b,j⟩,hbj,hbf⟩ := mem_image.mp (mem_filter.mp hf).1
    change edge (t a) i=e at hae
    change edge (t b) j=f at hbf
    have ha := (mem_filter.mp hai).2
    have hb := (mem_filter.mp hbj).2
    have hpa : p∈edge (t a) i := by rw [hae]; exact hpe
    have hpb : p∈edge (t b) j := by rw [hbf]; exact hpf
    obtain ⟨u,hu⟩ := base_selected_side hL hn line (radial p) cut hcut p (tip p) hpLine hpOrd
      (hrad p hp) (hprad p hp) (hsel p hp) (hpos p hp) (t a) (ht a) (hsides a) i ha.1 ha.2 hpa
    obtain ⟨v,hv⟩ := base_selected_side hL hn line (radial p) cut hcut p (tip p) hpLine hpOrd
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
    obtain ⟨⟨a,i⟩,hai,rfl⟩ := mem_image.mp (mem_filter.mp he).1
    exact edge_card (t a) i
  · ext p
    constructor
    · intro hp
      obtain ⟨e,he,hpe⟩ := mem_biUnion.mp hp
      exact hsub e he hpe
    · intro hp
      obtain ⟨e,he,hpe⟩ := hcover p hp
      exact mem_biUnion.mpr ⟨e,he,hpe⟩

theorem selected_degree_or_core_base {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n) (line : Fin n)
    (heven : n%2=0) (triples : ∀ p∈core n L, (supports n L p).card=3)
    (cut : Line ℝ) (hcut : ∀ p, affineEval cut p=0 ↔ affineEval (L line) p=0)
    (hvalid : cut.a≠0 ∨ cut.b≠0)
    (t : α → TriangleGeometry) (ht : ∀ a, Indexed n L (t a))
    (hsides : ∀ a i, edge (t a) i∈edges n L)
    (radial : Point → Fin n) (tip : Point → Point)
    (hrad : ∀ p∈ordinaryOnLine n L line, radial p≠line)
    (hprad : ∀ p∈ordinaryOnLine n L line, affineEval (L (radial p)) p=0)
    (hsel : ∀ p∈ordinaryOnLine n L line, {p,tip p}∈lineEdges n L (radial p))
    (hpos : ∀ p∈ordinaryOnLine n L line, 0<affineEval cut (tip p)) :
    (∃ p∈ordinaryOnLine n L line, degree t {p,tip p}≠1) ∨
      ∃ e∈touchingBases n L cut t, ∃ q∈e, q∈core n L := by
  classical
  by_cases allDegree : ∀ p∈ordinaryOnLine n L line, degree t {p,tip p}=1
  · right
    by_contra noCore
    have ordBase : ∀ e∈touchingBases n L cut t, ∀ q∈e, OrdinaryAt n L q := by
      intro e he q hq
      by_contra notOrd
      apply noCore
      have heBase := (mem_filter.mp he).1
      obtain ⟨⟨a,i⟩,hai,heq⟩ := mem_image.mp heBase
      have hInv : e∈edges n L := by simpa only [← heq,sideMap] using hsides a i
      have onCut := (mem_filter.mp hai).2.1
      have hLine := inventory_on_support n L hL hn line e hInv
        (fun p hp => (hcut p).mp (onCut p (by simpa only [heq] using hp)))
      have hVertex := (mem_filter.mp (inventory_vertex n L hL hn line hLine hq)).1
      exact ⟨e,he,q,hq,mem_filter.mpr ⟨hVertex,notOrd⟩⟩
    obtain ⟨card,pairwise,cover⟩ := actual_ordinary_base_cover n L hL hn line cut hcut hvalid
      t ht hsides radial tip hrad hprad hsel hpos allDegree ordBase
    exact triple_even_no_ordinary_pair_partition n L hL line heven triples
      (touchingBases n L cut t) card pairwise cover
  · left
    push Not at allDegree
    exact allDegree

#print axioms actual_ordinary_base_cover
#print axioms selected_degree_or_core_base
end Kobon.UpperOpenMathOrdinaryBaseCover
