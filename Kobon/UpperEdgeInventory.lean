import Kobon.UpperVertexBudget
import Kobon.UpperElementaryEdges
import Kobon.UpperTriangleIncidence
import Kobon.UpperSharedIncidence
import Mathlib.Data.Finset.Sort

/-!
# A finite geometric inventory of consecutive line segments

Intersection vertices on each actual line are ordered by a nonconstant affine
coordinate. Consecutive vertices form unordered real endpoint pairs. The
inventory counts those pairs exactly; disjointness between line inventories
is a consequence of nonparallelness, not a counting hypothesis.
-/
namespace Kobon.UpperEdgeInventory
open Cells UpperVertexBudget UpperTriangleIncidence Finset
open scoped BigOperators

noncomputable def coordinate (l : Line ℝ) (p : Point) : ℝ :=
  if l.b=0 then p.2 else p.1

noncomputable def parameter (l : Line ℝ) (x : ℝ) : Point :=
  if l.b=0 then (l.c/l.a,x) else (x,(l.c-l.a*x)/l.b)

theorem coordinate_parameter (l : Line ℝ) (x : ℝ) :
    coordinate l (parameter l x)=x := by
  unfold coordinate parameter
  split_ifs <;> rfl

theorem parameter_coordinate (l : Line ℝ) (valid : l.a≠0 ∨ l.b≠0)
    (p : Point) (hp : affineEval l p=0) : parameter l (coordinate l p)=p := by
  by_cases hb : l.b=0
  · have ha : l.a≠0 := valid.resolve_right (not_not.mpr hb)
    apply Prod.ext
    · simp only [parameter,coordinate,hb,ite_true]
      apply (div_eq_iff ha).mpr
      dsimp [affineEval] at hp
      rw [hb] at hp
      nlinarith
    · simp [parameter,coordinate,hb]
  · apply Prod.ext
    · simp [parameter,coordinate,hb]
    · simp only [parameter,coordinate,hb,ite_false]
      apply (div_eq_iff hb).mpr
      dsimp [affineEval] at hp
      nlinarith

theorem parameter_segment (l : Line ℝ) (x y u : ℝ) :
    parameter l ((1-u)*x+u*y)=segmentPoint (parameter l x) (parameter l y) u := by
  unfold parameter
  split_ifs <;> apply Prod.ext <;> dsimp [segmentPoint] <;> ring

section Arrangement
variable (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)

include hL hn in
theorem coordinate_injective_on_line (i : Fin n) {p q : Point}
    (hp : p∈onLine n L i) (hq : q∈onLine n L i)
    (he : coordinate (L i) p=coordinate (L i) q) : p=q := by
  classical
  rw [← parameter_coordinate (L i) (line_valid n L hL hn i) p (mem_filter.mp hp).2,
    ← parameter_coordinate (L i) (line_valid n L hL hn i) q (mem_filter.mp hq).2,he]

noncomputable def coordinates (i : Fin n) : Finset ℝ := by
  classical
  exact (onLine n L i).image (coordinate (L i))

include hL hn in
theorem coordinates_card (i : Fin n) : (coordinates n L i).card=(onLine n L i).card := by
  classical
  apply card_image_of_injOn
  intro p hp q hq he
  exact coordinate_injective_on_line n L hL hn i hp hq he

noncomputable def orderedPoint (i : Fin n) (k : Fin (coordinates n L i).card) : Point :=
  parameter (L i) ((coordinates n L i).orderEmbOfFin rfl k)

include hL hn in
theorem orderedPoint_mem (i : Fin n) (k : Fin (coordinates n L i).card) :
    orderedPoint n L i k∈onLine n L i := by
  classical
  have hx := (coordinates n L i).orderEmbOfFin_mem rfl k
  obtain ⟨p,hp,he⟩ := mem_image.mp hx
  rw [orderedPoint,← he,parameter_coordinate (L i) (line_valid n L hL hn i) p (mem_filter.mp hp).2]
  exact hp

theorem orderedPoint_injective (i : Fin n) : Function.Injective (orderedPoint n L i) := by
  intro a b he
  have hh := congrArg (coordinate (L i)) he
  simp only [orderedPoint,coordinate_parameter] at hh
  exact (coordinates n L i).orderEmbOfFin rfl |>.injective hh

include hL hn in
theorem orderedPoint_surjective (i : Fin n) {p : Point} (hp : p∈onLine n L i) :
    ∃ k : Fin (coordinates n L i).card, orderedPoint n L i k=p := by
  classical
  have hx : coordinate (L i) p∈coordinates n L i := mem_image.mpr ⟨p,hp,rfl⟩
  let x : coordinates n L i := ⟨coordinate (L i) p,hx⟩
  let k := ((coordinates n L i).orderIsoOfFin rfl).symm x
  have he : (coordinates n L i).orderEmbOfFin rfl k=coordinate (L i) p := by
    change (((coordinates n L i).orderIsoOfFin rfl) k).val=x.val
    rw [show ((coordinates n L i).orderIsoOfFin rfl) k=x from
      (coordinates n L i).orderIsoOfFin rfl |>.apply_symm_apply x]
  refine ⟨k,?_⟩
  rw [orderedPoint,he]
  exact parameter_coordinate (L i) (line_valid n L hL hn i) p (mem_filter.mp hp).2

noncomputable def intervalEdge (i : Fin n) (k : Fin ((coordinates n L i).card-1)) : Edge := by
  classical
  exact {orderedPoint n L i ⟨k.val,by have := k.isLt; omega⟩,
    orderedPoint n L i ⟨k.val+1,by have := k.isLt; omega⟩}

theorem intervalEdge_injective (i : Fin n) : Function.Injective (intervalEdge n L i) := by
  classical
  intro a b he
  have ha : orderedPoint n L i ⟨a.val,by have := a.isLt; omega⟩∈intervalEdge n L i b := by
    rw [← he]
    simp [intervalEdge]
  have hb : orderedPoint n L i ⟨b.val,by have := b.isLt; omega⟩∈intervalEdge n L i a := by
    rw [he]
    simp [intervalEdge]
  simp only [intervalEdge,mem_insert,mem_singleton] at ha hb
  have h1 : a.val=b.val ∨ a.val=b.val+1 := by
    rcases ha with h|h
    · exact Or.inl (congrArg (fun k : Fin (coordinates n L i).card => k.val) (orderedPoint_injective n L i h))
    · exact Or.inr (congrArg (fun k : Fin (coordinates n L i).card => k.val) (orderedPoint_injective n L i h))
  have h2 : b.val=a.val ∨ b.val=a.val+1 := by
    rcases hb with h|h
    · exact Or.inl (congrArg (fun k : Fin (coordinates n L i).card => k.val) (orderedPoint_injective n L i h))
    · exact Or.inr (congrArg (fun k : Fin (coordinates n L i).card => k.val) (orderedPoint_injective n L i h))
  apply Fin.ext
  omega

noncomputable def lineEdges (i : Fin n) : Finset Edge := by
  classical
  exact univ.image (intervalEdge n L i)

include hL hn in
theorem lineEdges_card (i : Fin n) : (lineEdges n L i).card=(onLine n L i).card-1 := by
  classical
  rw [lineEdges,card_image_of_injective _ (intervalEdge_injective n L i),card_univ,
    Fintype.card_fin,coordinates_card n L hL hn i]

include hL hn in
theorem edge_endpoints_on_line {i : Fin n} {e : Edge} (he : e∈lineEdges n L i) :
    ∀ p∈e, affineEval (L i) p=0 := by
  classical
  obtain ⟨k,_,rfl⟩ := mem_image.mp he
  intro p hp
  simp only [intervalEdge,mem_insert,mem_singleton] at hp
  rcases hp with rfl|rfl
  · exact (mem_filter.mp (orderedPoint_mem n L hL hn i _)).2
  · exact (mem_filter.mp (orderedPoint_mem n L hL hn i _)).2

theorem intervalEdge_card (i : Fin n) (k : Fin ((coordinates n L i).card-1)) :
    (intervalEdge n L i k).card=2 := by
  classical
  apply card_pair
  intro he
  have hh := congrArg Fin.val (orderedPoint_injective n L i he)
  simp only [Fin.val_mk] at hh
  omega

include hL hn in
theorem lineEdges_pairwise_disjoint :
    ((univ : Finset (Fin n)) : Set (Fin n)).PairwiseDisjoint (lineEdges n L) := by
  classical
  intro i _ j _ hij
  apply disjoint_left.mpr
  intro e hei hej
  obtain ⟨k,_,hek⟩ := mem_image.mp hei
  have hecard : e.card=2 := by rw [← hek]; exact intervalEdge_card n L i k
  obtain ⟨p,q,hpq,he⟩ := card_eq_two.mp hecard
  have hp : p∈e := by simp [he]
  have hq : q∈e := by simp [he]
  apply hpq
  exact two_lines_two_points (L i) (L j) p q
    (noParallel_any n L hL i j i.isLt j.isLt (fun h => hij (Fin.ext h)))
    (edge_endpoints_on_line n L hL hn hei p hp) (edge_endpoints_on_line n L hL hn hei q hq)
    (edge_endpoints_on_line n L hL hn hej p hp) (edge_endpoints_on_line n L hL hn hej q hq)

noncomputable def edges : Finset Edge := by
  classical
  exact univ.biUnion (lineEdges n L)

include hL hn in
/-- Exact number of distinct geometric consecutive segments. -/
theorem edge_cardinality :
    ((edges n L).card : ℤ)=(n : ℤ)*(n-2)-∑ p∈vertices n L,
      (supports n L p).card*((supports n L p).card-2 : ℤ) := by
  classical
  rw [edges,card_biUnion (lineEdges_pairwise_disjoint n L hL hn)]
  simp_rw [lineEdges_card n L hL hn]
  rw [Nat.cast_sum]
  exact line_interval_budget n L hL hn

/-- An intermediate ordered vertex lies in the open geometric segment. -/
theorem ordered_between (i : Fin n) (a b c : Fin (coordinates n L i).card)
    (hac : a<c) (hcb : c<b) :
    ∃ u : ℝ, 0<u ∧ u<1 ∧ orderedPoint n L i c=
      segmentPoint (orderedPoint n L i a) (orderedPoint n L i b) u := by
  let f := (coordinates n L i).orderEmbOfFin rfl
  have hxz : f a<f c := f.strictMono hac
  have hzy : f c<f b := f.strictMono hcb
  have hxy : 0<f b-f a := by linarith
  let u := (f c-f a)/(f b-f a)
  have hu : 0<u := div_pos (by linarith) hxy
  have hu1 : u<1 := by
    apply (div_lt_one hxy).mpr
    linarith
  have he : (1-u)*f a+u*f b=f c := by
    dsimp [u]
    field_simp
    ring
  refine ⟨u,hu,hu1,?_⟩
  change parameter (L i) (f c)=segmentPoint (parameter (L i) (f a)) (parameter (L i) (f b)) u
  rw [← parameter_segment,he]

include hL hn in
theorem no_index_between_elementary (i : Fin n) (a b c : Fin (coordinates n L i).card)
    (he : UpperElementaryEdges.Elementary n L i (orderedPoint n L i a) (orderedPoint n L i b))
    (hac : a<c) (hcb : c<b) : False := by
  classical
  obtain ⟨u,hu,hu1,hpoint⟩ := ordered_between n L i a b c hac hcb
  have hv := (mem_filter.mp (orderedPoint_mem n L hL hn i c)).1
  obtain ⟨ij,hij,hp⟩ := mem_image.mp hv
  have hne := (mem_offDiag.mp hij).2.2
  have hinc := (intersection_eq_iff n L hL ij.1 ij.2 hne (orderedPoint n L i c)).mp hp
  apply UpperElementaryEdges.no_vertex_in_relative_interior he ij.1 ij.2 hne u hu hu1
  · rw [← hpoint]
    exact hinc.1
  · rw [← hpoint]
    exact hinc.2

include hL hn in
theorem ordered_elementary_mem (i : Fin n) (a b : Fin (coordinates n L i).card)
    (he : UpperElementaryEdges.Elementary n L i (orderedPoint n L i a) (orderedPoint n L i b))
    (hab : a<b) : {orderedPoint n L i a,orderedPoint n L i b}∈lineEdges n L i := by
  classical
  have hsucc : a.val+1=b.val := by
    by_contra hh
    have hgap : a.val+1<b.val := by have := Fin.lt_def.mp hab; omega
    let c : Fin (coordinates n L i).card := ⟨a.val+1,by have := b.isLt; omega⟩
    exact no_index_between_elementary n L hL hn i a b c he
      (by change a.val<a.val+1; omega) (by exact hgap)
  let k : Fin ((coordinates n L i).card-1) := ⟨a.val,by have := b.isLt; omega⟩
  refine mem_image.mpr ⟨k,mem_univ k,?_⟩
  have hka : (⟨k.val,by have := k.isLt; omega⟩ : Fin (coordinates n L i).card)=a := Fin.ext rfl
  have hkb : (⟨k.val+1,by have := k.isLt; omega⟩ : Fin (coordinates n L i).card)=b := Fin.ext hsucc
  simp only [intervalEdge,hka,hkb]

include hL hn in
/-- Every actual elementary segment with arrangement-vertex endpoints occurs
in the finite consecutive-segment inventory of its supporting line. -/
theorem elementary_mem_lineEdges (i : Fin n) (p q : Point)
    (hp : p∈onLine n L i) (hq : q∈onLine n L i)
    (he : UpperElementaryEdges.Elementary n L i p q) : {p,q}∈lineEdges n L i := by
  classical
  obtain ⟨a,ha⟩ := orderedPoint_surjective n L hL hn i hp
  obtain ⟨b,hb⟩ := orderedPoint_surjective n L hL hn i hq
  rw [← ha,← hb] at he ⊢
  have hne : a≠b := by intro h; exact he.1 (congrArg (orderedPoint n L i) h)
  rcases lt_or_gt_of_ne hne with hab|hba
  · exact ordered_elementary_mem n L hL hn i a b he hab
  · rw [pair_comm]
    exact ordered_elementary_mem n L hL hn i b a he.symm hba

theorem intersection_mem_vertices (i j : Fin n) (hij : i≠j) :
    intersection (L i) (L j)∈vertices n L := by
  classical
  exact mem_image.mpr ⟨(i,j),mem_offDiag.mpr ⟨mem_univ _,mem_univ _,hij⟩,rfl⟩

theorem predicate_vertices (tri : Triple) (ht : TrianglePredicate n L tri) :
    let f := ofPredicate n L tri hL ht
    f.p∈vertices n L ∧ f.q∈vertices n L ∧ f.r∈vertices n L := by
  have hi : tri.i<n := by have := ht.1; have := ht.2.1; have := ht.2.2.1; omega
  have hj : tri.j<n := by have := ht.2.1; have := ht.2.2.1; omega
  have hk : tri.k<n := ht.2.2.1
  refine ⟨?_,?_,?_⟩
  · exact intersection_mem_vertices n L ⟨tri.i,hi⟩ ⟨tri.j,hj⟩
      (by intro h; have hh := congrArg (fun z : Fin n => z.val) h; simp only [Fin.val_mk] at hh; have := ht.1; omega)
  · exact intersection_mem_vertices n L ⟨tri.i,hi⟩ ⟨tri.k,hk⟩
      (by intro h; have hh := congrArg (fun z : Fin n => z.val) h; simp only [Fin.val_mk] at hh; have := ht.1; have := ht.2.1; omega)
  · exact intersection_mem_vertices n L ⟨tri.j,hj⟩ ⟨tri.k,hk⟩
      (by intro h; have hh := congrArg (fun z : Fin n => z.val) h; simp only [Fin.val_mk] at hh; have := ht.2.1; omega)

include hL hn in
/-- Every side of an actual certified arrangement triangle belongs to the
geometric edge inventory. -/
theorem predicate_side_mem_edges (tri : Triple) (ht : TrianglePredicate n L tri)
    (side : Fin 3) : edge (ofPredicate n L tri hL ht) side∈edges n L := by
  classical
  let f := ofPredicate n L tri hL ht
  have hv := predicate_vertices n L hL tri ht
  have hs := UpperElementaryEdges.predicate_all_sides_elementary n L tri hL ht
  have hi : tri.i<n := by have := ht.1; have := ht.2.1; have := ht.2.2.1; omega
  have hj : tri.j<n := by have := ht.2.1; have := ht.2.2.1; omega
  have hk : tri.k<n := ht.2.2.1
  fin_cases side
  · change {f.p,f.q}∈edges n L
    refine mem_biUnion.mpr ⟨⟨tri.i,hi⟩,mem_univ _,?_⟩
    exact elementary_mem_lineEdges n L hL hn ⟨tri.i,hi⟩ f.p f.q
      (mem_filter.mpr ⟨hv.1,f.Cp⟩) (mem_filter.mpr ⟨hv.2.1,f.Cq⟩) hs.1
  · change {f.q,f.r}∈edges n L
    refine mem_biUnion.mpr ⟨⟨tri.k,hk⟩,mem_univ _,?_⟩
    exact elementary_mem_lineEdges n L hL hn ⟨tri.k,hk⟩ f.q f.r
      (mem_filter.mpr ⟨hv.2.1,f.Aq⟩) (mem_filter.mpr ⟨hv.2.2,f.Ar⟩) hs.2.2
  · change {f.r,f.p}∈edges n L
    refine mem_biUnion.mpr ⟨⟨tri.j,hj⟩,mem_univ _,?_⟩
    exact elementary_mem_lineEdges n L hL hn ⟨tri.j,hj⟩ f.r f.p
      (mem_filter.mpr ⟨hv.2.2,f.Br⟩) (mem_filter.mpr ⟨hv.1,f.Bp⟩) hs.2.1.symm

include hL hn in
theorem certificate_sides_subset {α : Type*} [Fintype α]
    (tri : α → Triple) (ht : ∀ a, TrianglePredicate n L (tri a)) :
    usedEdges (fun a => ofPredicate n L (tri a) hL (ht a))⊆edges n L := by
  classical
  intro e he
  obtain ⟨a,_,rfl⟩ := mem_image.mp he
  exact predicate_side_mem_edges n L hL hn (tri a.1) (ht a.1) a.2

theorem predicate_side_vertices (tri : Triple) (ht : TrianglePredicate n L tri)
    (side : Fin 3) {p : Point} (hp : p∈edge (ofPredicate n L tri hL ht) side) :
    p∈vertices n L := by
  classical
  have hv := predicate_vertices n L hL tri ht
  fin_cases side
  all_goals simp only [edge,sideTriangle,cycle,Fin.reduceFinMk,ite_true,ite_false,
    mem_insert,mem_singleton] at hp
  all_goals rcases hp with rfl|rfl
  all_goals first | exact hv.1 | exact hv.2.1 | exact hv.2.2

theorem certificate_side_vertices {α : Type*} [Fintype α]
    (tri : α → Triple) (ht : ∀ a, TrianglePredicate n L (tri a))
    {e : Edge} (he : e∈usedEdges (fun a => ofPredicate n L (tri a) hL (ht a)))
    {p : Point} (hp : p∈e) : p∈vertices n L := by
  classical
  obtain ⟨a,_,rfl⟩ := mem_image.mp he
  exact predicate_side_vertices n L hL (tri a.1) (ht a.1) a.2 hp

include hL hn in
/-- The geometric defect identity, now derived for every finite injective
family of certified triangles. All vertex multiplicities, unused segments
and shared-edge classes are extracted from real coordinates. -/
theorem certificate_defect_identity {α : Type*} [Fintype α]
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a)) :
    let geometry := fun a => ofPredicate n L (tri a) hL (ht a)
    (n : ℤ)*(n-2)-3*Fintype.card α=
      (∑ p∈vertices n L, (supports n L p).card*((supports n L p).card-2 : ℤ))+
      (edges n L\usedEdges geometry).card-
      (UpperSharedIncidence.oneCoreEdges n L geometry).card-
      (UpperSharedIncidence.twoCoreEdges n L geometry).card := by
  classical
  let geometry := fun a => ofPredicate n L (tri a) hL (ht a)
  have hd : Pairwise (fun a b => Disjoint (geometry a).interior (geometry b).interior) := by
    intro a b hab
    exact distinct_interiors_disjoint n L _ _ hL (ht a) (ht b) (fun he => hab (hi he))
  have hbudget := UpperSharedIncidence.core_incidence n L geometry hd (edges n L)
    (certificate_sides_subset n L hL hn tri ht)
  have hc := congrArg (fun k : ℕ => (k : ℤ)) hbudget
  simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] at hc
  have he := edge_cardinality n L hL hn
  dsimp only [geometry] at hc
  rw [he] at hc
  linarith

end Arrangement

#print axioms orderedPoint_surjective
#print axioms lineEdges_pairwise_disjoint
#print axioms edge_cardinality
#print axioms elementary_mem_lineEdges
#print axioms certificate_defect_identity
end Kobon.UpperEdgeInventory


