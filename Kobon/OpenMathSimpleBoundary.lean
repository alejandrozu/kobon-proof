import Kobon.UpperEvenSimpleOptimality
import Mathlib.Data.Finset.Sigma

/-! Boundary vertices of actual simple line arrangements.  A triangle uses
an even number of sides at each of its vertices.  Consequently a vertex with
three bounded incident segments forces an unused segment. -/
namespace Kobon.OpenMathSimpleBoundary
open Cells FanGeometry UpperVertexBudget UpperTriangleIncidence UpperEdgeInventory Finset
open scoped BigOperators
set_option maxHeartbeats 0

noncomputable def incident (E : Finset Edge) (p : Point) : Finset Edge := by
  classical
  exact E.filter (fun e => p∈e)

theorem triangle_incident_even (t : TriangleGeometry) (p : Point) :
    Even ((univ.filter (fun i : Fin 3 => p∈edge t i)).card) := by
  classical
  have hpq : t.p≠t.q := nondegenerate_pair_ne _ _ _ t.nondegenerate
  have hpr : t.p≠t.r := by intro h; exact t.Ap (h ▸ t.Ar)
  have hqr : t.q≠t.r := by intro h; exact t.Bq (h ▸ t.Br)
  by_cases hp : p=t.p
  · have he : univ.filter (fun i : Fin 3 => p∈edge t i)={0,2} := by
      ext i
      fin_cases i <;> simp [hp,edge,sideTriangle,cycle,hpq,hpr,hqr]
    rw [he,card_pair (by decide : (0 : Fin 3)≠2)]
    norm_num
  by_cases hq : p=t.q
  · have he : univ.filter (fun i : Fin 3 => p∈edge t i)={0,1} := by
      ext i
      fin_cases i <;> simp [hq,edge,sideTriangle,cycle,hpq,hpr,hqr,Ne.symm hpq]
    rw [he,card_pair (by decide : (0 : Fin 3)≠1)]
    norm_num
  by_cases hr : p=t.r
  · have he : univ.filter (fun i : Fin 3 => p∈edge t i)={1,2} := by
      ext i
      fin_cases i <;> simp [hr,edge,sideTriangle,cycle,hpq,hpr,hqr,Ne.symm hpr,Ne.symm hqr]
    rw [he,card_pair (by decide : (1 : Fin 3)≠2)]
    norm_num
  have he : univ.filter (fun i : Fin 3 => p∈edge t i)=∅ := by
    ext i
    fin_cases i <;> simp [edge,sideTriangle,cycle,hp,hq,hr]
  rw [he]
  simp

theorem sideMap_injective_of_no_shared {α : Type*} [Fintype α]
    (t : α → TriangleGeometry)
    (hd : Pairwise (fun a b => Disjoint (t a).interior (t b).interior))
    (hs : sharedEdges t=∅) : Function.Injective (sideMap t) := by
  classical
  intro a b hab
  let e := sideMap t a
  have hu : e∈usedEdges t := mem_image.mpr ⟨a,mem_univ _,rfl⟩
  have h2 : degree t e≠2 := by
    intro h
    have he : e∈sharedEdges t := mem_filter.mpr ⟨hu,h⟩
    rw [hs] at he
    exact notMem_empty e he
  have hle : degree t e≤1 := by have := degree_le_two t hd e; omega
  have hh := card_le_one.mp hle
  exact hh a (mem_filter.mpr ⟨mem_univ _,rfl⟩) b
    (mem_filter.mpr ⟨mem_univ _,hab.symm⟩)

theorem used_incident_even {α : Type*} [Fintype α]
    (t : α → TriangleGeometry) (hs : Function.Injective (sideMap t))
    (p : Point) : Even ((incident (usedEdges t) p).card) := by
  classical
  have he : incident (usedEdges t) p=
      (univ.filter (fun a : α × Fin 3 => p∈edge (t a.1) a.2)).image (sideMap t) := by
    ext e
    simp only [incident,usedEdges,mem_filter,mem_image,mem_univ,true_and]
    constructor
    · rintro ⟨⟨a,ha⟩,hp⟩
      exact ⟨a,by change p∈sideMap t a; rw [ha]; exact hp,ha⟩
    · rintro ⟨a,hp,rfl⟩
      exact ⟨⟨a,rfl⟩,hp⟩
  rw [he,card_image_of_injective _ hs]
  have hc : (univ.filter (fun a : α × Fin 3 => p∈edge (t a.1) a.2)).card=
      ∑ a : α, (univ.filter (fun i : Fin 3 => p∈edge (t a) i)).card := by
    simp only [card_eq_sum_ones,sum_filter]
    rw [← univ_product_univ,sum_product]
  rw [hc]
  exact Finset.even_sum (fun a : α => (univ.filter (fun i : Fin 3 => p∈edge (t a) i)).card)
    (fun a _ => triangle_incident_even (t a) p)

noncomputable def indexNeighbors (m : ℕ) (k : Fin m) : Finset (Fin (m-1)) := by
  classical
  exact univ.filter (fun a => a.val=k.val ∨ a.val+1=k.val)

theorem indexNeighbors_card (m : ℕ) (hm : 2≤m) (k : Fin m) :
    (indexNeighbors m k).card=
      if k.val=0 ∨ k.val+1=m then 1 else 2 := by
  classical
  by_cases hk0 : k.val=0
  · let a : Fin (m-1) := ⟨0,by omega⟩
    have he : indexNeighbors m k={a} := by
      ext x
      simp only [indexNeighbors,mem_filter,mem_univ,true_and,mem_singleton]
      constructor
      · intro h
        apply Fin.ext
        dsimp [a]
        omega
      · intro h
        left
        have := congrArg Fin.val h
        dsimp [a] at this
        omega
    rw [he]
    simp [hk0]
  by_cases hkl : k.val+1=m
  · let a : Fin (m-1) := ⟨k.val-1,by have := k.isLt; omega⟩
    have he : indexNeighbors m k={a} := by
      ext x
      simp only [indexNeighbors,mem_filter,mem_univ,true_and,mem_singleton]
      constructor
      · intro h
        apply Fin.ext
        dsimp [a]
        have := x.isLt
        omega
      · intro h
        right
        have := congrArg Fin.val h
        dsimp [a] at this
        omega
    rw [he]
    simp [hkl]
  let a : Fin (m-1) := ⟨k.val-1,by have := k.isLt; omega⟩
  let b : Fin (m-1) := ⟨k.val,by have := k.isLt; omega⟩
  have hab : a≠b := by
    intro h
    have := congrArg Fin.val h
    dsimp [a,b] at this
    omega
  have he : indexNeighbors m k={a,b} := by
    ext x
    simp only [indexNeighbors,mem_filter,mem_univ,true_and,mem_insert,mem_singleton]
    constructor
    · intro h
      rcases h with h|h
      · exact Or.inr (Fin.ext h)
      · left
        apply Fin.ext
        dsimp [a]
        omega
    · rintro (h|h)
      · right
        have := congrArg Fin.val h
        dsimp [a] at this
        omega
      · left
        exact congrArg Fin.val h
  rw [he,card_pair hab]
  simp [hk0,hkl]

theorem line_incident_card (n : ℕ) (L : ℕ → Line ℝ) (i : Fin n)
    (hm : 2≤(coordinates n L i).card) (k : Fin (coordinates n L i).card) :
    (incident (lineEdges n L i) (orderedPoint n L i k)).card=
      if k.val=0 ∨ k.val+1=(coordinates n L i).card then 1 else 2 := by
  classical
  have he : incident (lineEdges n L i) (orderedPoint n L i k)=
      (indexNeighbors (coordinates n L i).card k).image (intervalEdge n L i) := by
    ext e
    simp only [incident,lineEdges,mem_filter,mem_image,mem_univ,true_and]
    constructor
    · rintro ⟨⟨a,rfl⟩,hp⟩
      refine ⟨a,?_,rfl⟩
      simp only [indexNeighbors,mem_filter,mem_univ,true_and]
      simp only [intervalEdge,mem_insert,mem_singleton] at hp
      rcases hp with h|h
      · left
        exact (congrArg Fin.val (orderedPoint_injective n L i h)).symm
      · right
        exact (congrArg Fin.val (orderedPoint_injective n L i h)).symm
    · rintro ⟨a,ha,rfl⟩
      refine ⟨⟨a,rfl⟩,?_⟩
      simp only [indexNeighbors,mem_filter,mem_univ,true_and] at ha
      simp only [intervalEdge,mem_insert,mem_singleton]
      rcases ha with h|h
      · left
        exact congrArg (orderedPoint n L i) (Fin.ext h.symm)
      · right
        exact congrArg (orderedPoint n L i) (Fin.ext h.symm)
  rw [he,card_image_of_injective _ (intervalEdge_injective n L i)]
  exact indexNeighbors_card _ hm k

noncomputable def lineTerminals (n : ℕ) (L : ℕ → Line ℝ) (i : Fin n) : Finset Point := by
  classical
  exact (univ.filter (fun k : Fin (coordinates n L i).card =>
    k.val=0 ∨ k.val+1=(coordinates n L i).card)).image (orderedPoint n L i)

noncomputable def terminalsAt (n : ℕ) (L : ℕ → Line ℝ) (p : Point) : Finset (Fin n) := by
  classical
  exact univ.filter (fun i => p∈lineTerminals n L i)

noncomputable def singleTerminals (n : ℕ) (L : ℕ → Line ℝ) : Finset Point := by
  classical
  exact (vertices n L).filter (fun p => (terminalsAt n L p).card=1)

noncomputable def doubleTerminals (n : ℕ) (L : ℕ → Line ℝ) : Finset Point := by
  classical
  exact (vertices n L).filter (fun p => (terminalsAt n L p).card=2)

theorem terminal_index_iff (n : ℕ) (L : ℕ → Line ℝ) (i : Fin n)
    (k : Fin (coordinates n L i).card) :
    orderedPoint n L i k∈lineTerminals n L i ↔
      k.val=0 ∨ k.val+1=(coordinates n L i).card := by
  classical
  simp only [lineTerminals,mem_image,mem_filter,mem_univ,true_and]
  constructor
  · rintro ⟨a,ha,he⟩
    have heq : a=k := orderedPoint_injective n L i he
    simpa only [heq] using ha
  · intro hk
    exact ⟨k,hk,rfl⟩

theorem lineTerminals_card (n : ℕ) (L : ℕ → Line ℝ) (i : Fin n)
    (hm : 2≤(coordinates n L i).card) : (lineTerminals n L i).card=2 := by
  classical
  let m := (coordinates n L i).card
  let a : Fin m := ⟨0,by omega⟩
  let b : Fin m := ⟨m-1,by omega⟩
  have hab : a≠b := by
    intro h
    have := congrArg Fin.val h
    dsimp [a,b] at this
    omega
  have he : univ.filter (fun k : Fin m => k.val=0 ∨ k.val+1=m)={a,b} := by
    ext k
    simp only [mem_filter,mem_univ,true_and,mem_insert,mem_singleton]
    constructor
    · rintro (h|h)
      · exact Or.inl (Fin.ext h)
      · right
        apply Fin.ext
        dsimp [b]
        omega
    · rintro (h|h)
      · left
        exact congrArg Fin.val h
      · right
        have := congrArg Fin.val h
        dsimp [b] at this
        omega
  unfold lineTerminals
  rw [card_image_of_injective _ (orderedPoint_injective n L i),he,card_pair hab]

theorem terminal_mem_onLine (n : ℕ) (L : ℕ → Line ℝ) (hp : NoParallel n L)
    (hn : 2≤n) (i : Fin n) {p : Point} (ht : p∈lineTerminals n L i) :
    p∈onLine n L i := by
  classical
  obtain ⟨k,hk,rfl⟩ := mem_image.mp ht
  exact orderedPoint_mem n L hp hn i k

theorem simple_ordinary (n : ℕ) (L : ℕ → Line ℝ) (hp : NoParallel n L)
    (hs : NoConcurrent n L) {p : Point} (hv : p∈vertices n L) : OrdinaryAt n L p := by
  classical
  obtain ⟨⟨i,j⟩,hij,rfl⟩ := mem_image.mp hv
  exact UpperSimpleOptimality.ordinary_intersection n L hp hs i j (mem_offDiag.mp hij).2.2

theorem simple_clean (n : ℕ) (L : ℕ → Line ℝ) (hp : NoParallel n L)
    (hs : NoConcurrent n L) (i : Fin n) : UpperCleanHalfplane.Clean n L i := by
  intro p hv
  exact simple_ordinary n L hp hs (mem_filter.mp hv).1

theorem simple_coordinate_card (n : ℕ) (L : ℕ → Line ℝ) (hp : NoParallel n L)
    (hs : NoConcurrent n L) (hn : 3≤n) (i : Fin n) :
    (coordinates n L i).card=n-1 := by
  rw [coordinates_card n L hp (by omega),
    UpperCleanHalfplane.clean_crossing_card n L hp i (simple_clean n L hp hs i)]

theorem incident_on_line_card (n : ℕ) (L : ℕ → Line ℝ) (hp : NoParallel n L)
    (hn : 2≤n) (i : Fin n) (hm : 2≤(coordinates n L i).card)
    {p : Point} (hv : p∈onLine n L i) :
    (incident (lineEdges n L i) p).card=
      if p∈lineTerminals n L i then 1 else 2 := by
  classical
  obtain ⟨k,rfl⟩ := orderedPoint_surjective n L hp hn i hv
  rw [line_incident_card n L i hm k]
  simp only [terminal_index_iff]

theorem terminalsAt_le_two (n : ℕ) (L : ℕ → Line ℝ) (hp : NoParallel n L)
    (hn : 2≤n) {p : Point} (ho : OrdinaryAt n L p) :
    (terminalsAt n L p).card≤2 := by
  classical
  have hsub : terminalsAt n L p⊆supports n L p := by
    intro i hi
    have ht := terminal_mem_onLine n L hp hn i (mem_filter.mp hi).2
    exact mem_filter.mpr ⟨mem_univ _,(mem_filter.mp ht).2⟩
  have hc := card_le_card hsub
  rw [UpperCoreExtraction.ordinary_iff_support_card n L p |>.mp ho] at hc
  exact hc

theorem ordinary_incident_terminal_identity (n : ℕ) (L : ℕ → Line ℝ)
    (hp : NoParallel n L) (hs : NoConcurrent n L) (hn : 3≤n)
    {p : Point} (hv : p∈vertices n L) :
    (incident (edges n L) p).card+(terminalsAt n L p).card=4 := by
  classical
  obtain ⟨i,j,hij,hspan⟩ := simple_ordinary n L hp hs hv
  have hpi : p∈onLine n L i := mem_filter.mpr ⟨hv,(hspan i).mpr (Or.inl rfl)⟩
  have hpj : p∈onLine n L j := mem_filter.mpr ⟨hv,(hspan j).mpr (Or.inr rfl)⟩
  have he : incident (edges n L) p=
      incident (lineEdges n L i) p∪incident (lineEdges n L j) p := by
    ext e
    simp only [incident,mem_filter,mem_union]
    constructor
    · rintro ⟨he,hpe⟩
      obtain ⟨r,hr,her⟩ := mem_biUnion.mp he
      have hrp := edge_endpoints_on_line n L hp (by omega) her p hpe
      rcases (hspan r).mp hrp with rfl|rfl
      · exact Or.inl ⟨her,hpe⟩
      · exact Or.inr ⟨her,hpe⟩
    · rintro (⟨hei,hpe⟩|⟨hej,hpe⟩)
      · exact ⟨mem_biUnion.mpr ⟨i,mem_univ _,hei⟩,hpe⟩
      · exact ⟨mem_biUnion.mpr ⟨j,mem_univ _,hej⟩,hpe⟩
  have hdisj : Disjoint (incident (lineEdges n L i) p) (incident (lineEdges n L j) p) :=
    Disjoint.mono (filter_subset _ _) (filter_subset _ _)
      (lineEdges_pairwise_disjoint n L hp (by omega) (mem_univ _) (mem_univ _) hij)
  have hterm : terminalsAt n L p=({i,j} : Finset (Fin n)).filter
      (fun r => p∈lineTerminals n L r) := by
    ext r
    simp only [terminalsAt,mem_filter,mem_univ,true_and,mem_insert,mem_singleton]
    constructor
    · intro ht
      exact ⟨(hspan r).mp (mem_filter.mp (terminal_mem_onLine n L hp (by omega) r ht)).2,ht⟩
    · exact And.right
  have htc : (terminalsAt n L p).card=
      (if p∈lineTerminals n L i then 1 else 0)+(if p∈lineTerminals n L j then 1 else 0) := by
    rw [hterm,card_eq_sum_ones,sum_filter,sum_pair hij]
  have hmi : 2≤(coordinates n L i).card := by rw [simple_coordinate_card n L hp hs hn i]; omega
  have hmj : 2≤(coordinates n L j).card := by rw [simple_coordinate_card n L hp hs hn j]; omega
  rw [he,card_union_of_disjoint hdisj,incident_on_line_card n L hp (by omega) i hmi hpi,
    incident_on_line_card n L hp (by omega) j hmj hpj,htc]
  split_ifs <;> omega

theorem simple_single_forces_unused {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hp : NoParallel n L) (hs : NoConcurrent n L)
    (hn : 3≤n) (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    {p : Point} (hv : p∈singleTerminals n L) :
    ∃ e∈edges n L\usedEdges (fun a => ofPredicate n L (tri a) hp (ht a)), p∈e := by
  classical
  let t := fun a => ofPredicate n L (tri a) hp (ht a)
  have hdegree := ordinary_incident_terminal_identity n L hp hs hn (mem_filter.mp hv).1
  rw [(mem_filter.mp hv).2] at hdegree
  have hthree : (incident (edges n L) p).card=3 := by omega
  have hdisjoint : Pairwise (fun a b => Disjoint (t a).interior (t b).interior) := by
    intro a b hab
    exact distinct_interiors_disjoint n L _ _ hp (ht a) (ht b) (fun he => hab (hi he))
  have hinj := sideMap_injective_of_no_shared t hdisjoint
    (UpperEvenSimpleOptimality.shared_empty n L hp hs tri hi ht)
  have heven := used_incident_even t hinj p
  by_contra hno
  have he : incident (edges n L) p=incident (usedEdges t) p := by
    ext e
    simp only [incident,mem_filter]
    constructor
    · rintro ⟨he,hpe⟩
      refine ⟨?_,hpe⟩
      by_contra heu
      exact hno ⟨e,mem_sdiff.mpr ⟨he,heu⟩,hpe⟩
    · rintro ⟨heu,hpe⟩
      exact ⟨certificate_sides_subset n L hp (by omega) tri ht heu,hpe⟩
  rw [← he,hthree] at heven
  obtain ⟨a,ha⟩ := heven
  omega

/-- Single-terminal ordinary vertices consume actual unused edge endpoints;
the same unused segment can receive at most two such vertex charges. -/
theorem certificate_single_terminal_budget {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hp : NoParallel n L) (hs : NoConcurrent n L)
    (hn : 3≤n) (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a)) :
    (singleTerminals n L).card≤
      2*(edges n L\usedEdges (fun a => ofPredicate n L (tri a) hp (ht a))).card := by
  classical
  let U := edges n L\usedEdges (fun a => ofPredicate n L (tri a) hp (ht a))
  let β := {p : Point // p∈singleTerminals n L}
  have hex : ∀ p : β, ∃ e∈U, p.val∈e := fun p =>
    simple_single_forces_unused n L hp hs hn tri hi ht p.property
  choose charge hcharge using hex
  let f : β → (Σ _e : Edge, Point) := fun p => ⟨charge p,p.val⟩
  have hf : Function.Injective f := by
    intro p q he
    apply Subtype.ext
    exact congrArg (fun z : Σ _e : Edge, Point => z.2) he
  have hsub : univ.image f⊆U.sigma id := by
    intro z hz
    obtain ⟨p,hp,rfl⟩ := mem_image.mp hz
    exact mem_sigma.mpr (hcharge p)
  have hh := card_le_card hsub
  rw [card_image_of_injective _ hf,card_univ,card_sigma] at hh
  dsimp only [id_eq] at hh
  have hsum : (∑ e∈U,e.card)=2*U.card := by
    calc
      (∑ e∈U,e.card)=∑ _e∈U,2 := sum_congr rfl fun e he =>
        UpperCleanCharging.inventory_card_two n L (mem_sdiff.mp he).1
      _=2*U.card := by simp [Nat.mul_comm]
  rw [hsum] at hh
  simpa only [β,Fintype.card_coe] using hh

theorem terminal_total (n : ℕ) (L : ℕ → Line ℝ) (hp : NoParallel n L)
    (hs : NoConcurrent n L) (hn : 3≤n) :
    (∑ p∈vertices n L,(terminalsAt n L p).card)=2*n := by
  classical
  have hline (i : Fin n) :
      (∑ p∈vertices n L,if p∈lineTerminals n L i then 1 else 0 : ℕ)=2 := by
    have hf : (vertices n L).filter (fun p => p∈lineTerminals n L i)=lineTerminals n L i := by
      ext p
      simp only [mem_filter]
      constructor
      · exact And.right
      · intro ht
        exact ⟨(mem_filter.mp (terminal_mem_onLine n L hp (by omega) i ht)).1,ht⟩
    have hm : 2≤(coordinates n L i).card := by rw [simple_coordinate_card n L hp hs hn i]; omega
    calc
      (∑ p∈vertices n L,if p∈lineTerminals n L i then 1 else 0 : ℕ)=
          ((vertices n L).filter (fun p => p∈lineTerminals n L i)).card := by
        simp only [card_eq_sum_ones,sum_filter]
      _=(lineTerminals n L i).card := congrArg Finset.card hf
      _=2 := lineTerminals_card n L i hm
  calc
    (∑ p∈vertices n L,(terminalsAt n L p).card)=
        ∑ p∈vertices n L,∑ i : Fin n,if p∈lineTerminals n L i then 1 else 0 := by
      simp only [terminalsAt,card_eq_sum_ones,sum_filter]
    _=∑ i : Fin n,∑ p∈vertices n L,if p∈lineTerminals n L i then 1 else 0 := sum_comm
    _=∑ _i : Fin n,2 := sum_congr rfl fun i _ => hline i
    _=2*n := by simp [Nat.mul_comm]

/-- The two outer endpoints of each actual line are counted once or twice
according to how many supporting lines terminate there. -/
theorem terminal_partition (n : ℕ) (L : ℕ → Line ℝ) (hp : NoParallel n L)
    (hs : NoConcurrent n L) (hn : 3≤n) :
    (singleTerminals n L).card+2*(doubleTerminals n L).card=2*n := by
  classical
  have hc (p : Point) (hv : p∈vertices n L) :
      (terminalsAt n L p).card=
      (if (terminalsAt n L p).card=1 then 1 else 0)+
      2*(if (terminalsAt n L p).card=2 then 1 else 0) := by
    have := terminalsAt_le_two n L hp (by omega) (simple_ordinary n L hp hs hv)
    split_ifs <;> omega
  have hh := terminal_total n L hp hs hn
  have he : (∑ p∈vertices n L,(terminalsAt n L p).card)=
      (singleTerminals n L).card+2*(doubleTerminals n L).card := by
    rw [sum_congr rfl hc,sum_add_distrib,← mul_sum]
    simp [sum_boole,singleTerminals,doubleTerminals]
  rw [he] at hh
  exact hh

/-- Any finite injective certified triangle family in a simple arrangement
leaves at least n-U double-terminal vertices, with U its actual unused
segment count.  No exterior visibility or insertion premise is assumed. -/
theorem certificate_double_terminal_budget {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hp : NoParallel n L) (hs : NoConcurrent n L)
    (hn : 3≤n) (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a)) :
    n≤(doubleTerminals n L).card+
      (edges n L\usedEdges (fun a => ofPredicate n L (tri a) hp (ht a))).card := by
  have hpart := terminal_partition n L hp hs hn
  have hbudget := certificate_single_terminal_budget n L hp hs hn tri hi ht
  omega

/-- Geometric defect bounds the number of lost double-terminal vertices.
This is a bound for every certified simple arrangement, not an assumption
that an arrangement has a particular boundary form. -/
theorem certificate_boundary_defect {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hp : NoParallel n L) (hs : NoConcurrent n L)
    (hn : 3≤n) (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a)) :
    (n : ℤ)-((n : ℤ)*(n-2)-3*Fintype.card α)≤(doubleTerminals n L).card := by
  let G := fun a => ofPredicate n L (tri a) hp (ht a)
  have hc := UpperSimpleOptimality.core_empty n L hp hs
  have hshared := UpperEvenSimpleOptimality.shared_empty n L hp hs tri hi ht
  have hid := UpperCoreExtraction.defect_identity n L hp (by omega) tri hi ht
  have he : (n : ℤ)*(n-2)-3*Fintype.card α=((edges n L\usedEdges G).card : ℤ) := by
    simpa only [hc,sum_empty,zero_add,UpperSharedIncidence.oneCoreEdges,
      UpperSharedIncidence.twoCoreEdges,hshared,filter_empty,sdiff_empty,card_empty,
      Nat.cast_zero,sub_zero] using hid
  have hb : (n : ℤ)≤(doubleTerminals n L).card+(edges n L\usedEdges G).card := by
    exact_mod_cast certificate_double_terminal_budget n L hp hs hn tri hi ht
  rw [he]
  linarith

theorem terminal_extreme_coordinate (n : ℕ) (L : ℕ → Line ℝ) (hp : NoParallel n L)
    (hn : 2≤n) (i : Fin n) {p : Point} (ht : p∈lineTerminals n L i) :
    (∀ q∈onLine n L i,coordinate (L i) p≤coordinate (L i) q) ∨
    (∀ q∈onLine n L i,coordinate (L i) q≤coordinate (L i) p) := by
  classical
  obtain ⟨k,hk,rfl⟩ := mem_image.mp ht
  have hbound := (mem_filter.mp hk).2
  rcases hbound with hfirst|hlast
  · left
    intro q hq
    obtain ⟨j,rfl⟩ := orderedPoint_surjective n L hp hn i hq
    simp only [orderedPoint,coordinate_parameter]
    apply (coordinates n L i).orderEmbOfFin rfl |>.monotone
    change k.val≤j.val
    omega
  · right
    intro q hq
    obtain ⟨j,rfl⟩ := orderedPoint_surjective n L hp hn i hq
    simp only [orderedPoint,coordinate_parameter]
    apply (coordinates n L i).orderEmbOfFin rfl |>.monotone
    change j.val≤k.val
    have := j.isLt
    omega

#print axioms triangle_incident_even
#print axioms used_incident_even
#print axioms simple_single_forces_unused
#print axioms certificate_single_terminal_budget
#print axioms terminal_partition
#print axioms certificate_double_terminal_budget
#print axioms certificate_boundary_defect
#print axioms terminal_extreme_coordinate

end Kobon.OpenMathSimpleBoundary
