import Kobon.UpperOpenMathOrdinaryLineCharge
import Kobon.UpperOpenMathRayResources

/-!
# All-line ordinary crossing parity charge with explicit two-mode capacity

Unused transverse sides pay at most twice, ordinary-to-core shared sides
pay once in each of the transverse and base modes, and nonshared core-ended
bases pay from actual core endpoint incidences. Thus `n <= 2U + 2D1 + C`.
The doubled D1 coefficient is retained explicitly; improving it requires an
additional global reconciliation and is not assumed here.
-/
namespace Kobon.UpperOpenMathOrdinaryGlobalCharge
open Cells FanGeometry UpperVertexBudget UpperTriangleIncidence UpperSharedIncidence
  UpperEdgeInventory UpperCoreExtraction UpperCleanCharging UpperOpenMathCoreCapacity
  UpperOpenMathOrdinaryCutParity UpperOpenMathOrdinaryLineCharge Finset
open scoped BigOperators

theorem transverse_charge_count {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (A : Finset (Fin n))
    (charges : ∀ i∈A, TransverseCharge n L (fun a => ofPredicate n L (tri a) hL (ht a)) i) :
    let G := fun a => ofPredicate n L (tri a) hL (ht a)
    A.card≤2*(edges n L\usedEdges G).card+(oneCoreEdges n L G).card := by
  classical
  let G := fun a => ofPredicate n L (tri a) hL (ht a)
  let U := edges n L\usedEdges G
  let D := oneCoreEdges n L G
  let B := U∪D
  let β := {i : Fin n // i∈A}
  have hex : ∀ i : β, ∃ e : Edge, ∃ p : Point, ∃ r : Fin n,
      e∈B ∧ p∈e ∧ p∈ordinaryOnLine n L i.val ∧ r≠i.val ∧ e∈lineEdges n L r := by
    intro i
    obtain ⟨e,he,p,hpe,hp,r,hr,her⟩ := charges i.val i.property
    exact ⟨e,p,r,mem_union.mpr he,hpe,hp,hr,her⟩
  choose charge point support hcharge using hex
  let f : β → (Σ _e : Edge, Point) := fun i => ⟨charge i,point i⟩
  have hf : Function.Injective f := by
    intro i j he
    have heq : charge i=charge j := congrArg Sigma.fst he
    have hpq : point i=point j := congrArg (fun z : Σ _e : Edge, Point => z.2) he
    apply Subtype.ext
    have hpi := (hcharge i).2.2.1
    have hpj := (hcharge j).2.2.1
    apply charge_line_unique n L hL hn i.val j.val (support i) (support j)
      (charge i) (point i) (hcharge i).2.1 (mem_filter.mp hpi).2
      (hcharge i).2.2.2.1 (hcharge j).2.2.2.1 (hcharge i).2.2.2.2
    · simpa only [heq] using (hcharge j).2.2.2.2
    · exact (mem_filter.mp (mem_filter.mp hpi).1).2
    · simpa only [hpq] using (mem_filter.mp (mem_filter.mp hpj).1).2
  let target := B.sigma (fun e => e.filter (OrdinaryAt n L))
  have hsub : univ.image f⊆target := by
    intro z hz
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hz
    exact mem_sigma.mpr ⟨(hcharge i).1,mem_filter.mpr
      ⟨(hcharge i).2.1,(mem_filter.mp (hcharge i).2.2.1).2⟩⟩
  have hcTarget : A.card≤target.card := by
    have hh := card_le_card hsub
    rw [card_image_of_injective _ hf,card_univ] at hh
    simpa only [β,Fintype.card_coe] using hh
  have hUD : Disjoint U D := by
    apply disjoint_left.mpr
    intro e heU heD
    exact (mem_sdiff.mp heU).2 (mem_filter.mp (mem_filter.mp heD).1).1
  have hU (e : Edge) (he : e∈U) : (e.filter (OrdinaryAt n L)).card≤2 := by
    have hh := card_le_card (filter_subset (OrdinaryAt n L) e)
    rw [inventory_card_two n L (mem_sdiff.mp he).1] at hh
    exact hh
  have hD (e : Edge) (he : e∈D) : (e.filter (OrdinaryAt n L)).card=1 :=
    oneCore_ordinary_card n L hL tri hi ht he
  have htarget : target.card≤2*U.card+D.card := by
    rw [card_sigma,sum_union hUD]
    have hsU : (∑ e∈U, (e.filter (OrdinaryAt n L)).card)≤2*U.card := by
      calc
        _≤∑ _e∈U, 2 := sum_le_sum hU
        _=2*U.card := by simp [Nat.mul_comm]
    have hsD : (∑ e∈D, (e.filter (OrdinaryAt n L)).card)=D.card := by
      calc
        _=∑ _e∈D, 1 := sum_congr rfl hD
        _=D.card := by simp
    rw [hsD]
    exact Nat.add_le_add_right hsU D.card
  exact hcTarget.trans htarget

noncomputable def nonsharedCoreEdges {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (G : α → TriangleGeometry) : Finset Edge := by
  classical
  exact (edges n L\sharedEdges G).filter (fun e => (e∩core n L).Nonempty)

theorem nonshared_core_edge_capacity {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (G : α → TriangleGeometry) :
    (nonsharedCoreEdges n L G).card≤nonsharedCoreIncidences n L G := by
  classical
  have hs : nonsharedCoreEdges n L G⊆edges n L\sharedEdges G := filter_subset _ _
  calc
    _=∑ _e∈nonsharedCoreEdges n L G, 1 := by simp
    _≤∑ e∈nonsharedCoreEdges n L G, (e∩core n L).card :=
      sum_le_sum (fun e he => card_pos.mpr (mem_filter.mp he).2)
    _≤∑ e∈edges n L\sharedEdges G, (e∩core n L).card :=
      sum_le_sum_of_subset_of_nonneg hs (fun _ _ _ => Nat.zero_le _)
    _=nonsharedCoreIncidences n L G := rfl

theorem core_base_charge_count {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (ht : ∀ a, TrianglePredicate n L (tri a))
    (A : Finset (Fin n))
    (charges : ∀ i∈A, CoreBaseCharge n L (fun a => ofPredicate n L (tri a) hL (ht a)) i) :
    let G := fun a => ofPredicate n L (tri a) hL (ht a)
    A.card≤(oneCoreEdges n L G).card+nonsharedCoreIncidences n L G := by
  classical
  let G := fun a => ofPredicate n L (tri a) hL (ht a)
  let D := oneCoreEdges n L G
  let N := nonsharedCoreEdges n L G
  let β := {i : Fin n // i∈A}
  have hex : ∀ i : β, ∃ e : Edge, e∈lineEdges n L i.val ∧ e∈D∪N := by
    intro i
    obtain ⟨e,he,q,hqe,hqc,hclass⟩ := charges i.val i.property
    refine ⟨e,he,?_⟩
    rcases hclass with hclass|hclass
    · exact mem_union.mpr (Or.inl hclass)
    · exact mem_union.mpr (Or.inr (mem_filter.mpr ⟨hclass,⟨q,mem_inter.mpr ⟨hqe,hqc⟩⟩⟩))
  choose charge hcharge using hex
  have inj : Function.Injective charge := by
    intro i j he
    apply Subtype.ext
    by_contra hne
    exact disjoint_left.mp (lineEdges_pairwise_disjoint n L hL hn (mem_univ _) (mem_univ _) hne)
      (hcharge i).1 (by simpa only [he] using (hcharge j).1)
  have sub : univ.image charge⊆D∪N := by
    intro e he
    obtain ⟨i,hi,rfl⟩ := mem_image.mp he
    exact (hcharge i).2
  have count := card_le_card sub
  rw [card_image_of_injective _ inj,card_univ] at count
  have disj : Disjoint D N := by
    apply disjoint_left.mpr
    intro e hd hn
    exact (mem_sdiff.mp (mem_filter.mp hn).1).2 (mem_filter.mp hd).1
  rw [card_union_of_disjoint disj] at count
  have nc := nonshared_core_edge_capacity n L G
  have acount : A.card≤D.card+N.card := by simpa only [β,Fintype.card_coe] using count
  exact acount.trans (Nat.add_le_add_left nc D.card)

theorem certificate_all_line_parity_budget {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 4≤n)
    (heven : n%2=0) (triples : ∀ p∈core n L, (supports n L p).card=3)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a)) :
    let G := fun a => ofPredicate n L (tri a) hL (ht a)
    n≤2*(edges n L\usedEdges G).card+2*(oneCoreEdges n L G).card+nonsharedCoreIncidences n L G := by
  classical
  let G := fun a => ofPredicate n L (tri a) hL (ht a)
  let A := (univ : Finset (Fin n)).filter (TransverseCharge n L G)
  let B := (univ : Finset (Fin n))\A
  have aCharge : ∀ i∈A, TransverseCharge n L G i := fun i hi => (mem_filter.mp hi).2
  have bCharge : ∀ i∈B, CoreBaseCharge n L G i := by
    intro i hiB
    rcases certificate_all_line_charge n L hL hn heven triples tri hi ht i with ht|hb
    · exact False.elim ((mem_sdiff.mp hiB).2 (mem_filter.mpr ⟨mem_univ i,ht⟩))
    · exact hb
  have aCount := transverse_charge_count n L hL (by omega) tri hi ht A aCharge
  have bCount := core_base_charge_count n L hL (by omega) tri ht B bCharge
  have sumCounts := card_sdiff_add_card_eq_card (subset_univ A)
  simp only [card_univ,Fintype.card_fin] at sumCounts
  change B.card+A.card=n at sumCounts
  dsimp only at aCount bCount ⊢
  omega

theorem certificate_triple_even_defect_charge {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 4≤n)
    (heven : n%2=0) (triples : ∀ p∈core n L, (supports n L p).card=3)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a)) :
    let G := fun a => ofPredicate n L (tri a) hL (ht a)
    (n : ℤ)-3*(oneCoreEdges n L G).card+UpperOpenMathRayResources.coreEndRays n L≤
      2*((n : ℤ)*(n-2)-3*Fintype.card α) := by
  classical
  let G := fun a => ofPredicate n L (tri a) hL (ht a)
  have hN := certificate_all_line_parity_budget n L hL hn heven triples tri hi ht
  have hNZ : (n : ℤ)≤2*(edges n L\usedEdges G).card+
      2*(oneCoreEdges n L G).card+nonsharedCoreIncidences n L G := by exact_mod_cast hN
  have hid := UpperOpenMathRayResources.certificate_defect_ray_identity n L hL (by omega) tri hi ht
  have hweight : (∑ p∈core n L, (supports n L p).card*((supports n L p).card-3 : ℤ))=0 := by
    apply sum_eq_zero
    intro p hp
    rw [triples p hp]
    norm_num
  rw [hweight] at hid
  dsimp only at hid
  change (n : ℤ)-3*(oneCoreEdges n L G).card+UpperOpenMathRayResources.coreEndRays n L≤_
  linarith

/-- An even all-triple arrangement with no ordinary-to-core shared sides
obeys Blanc's even polynomial bound, even when the core is nonempty. -/
theorem certificate_triple_even_no_ordinary_core_upper {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 4≤n)
    (heven : n%2=0) (triples : ∀ p∈core n L, (supports n L p).card=3)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (noOrdinaryCore : (oneCoreEdges n L (fun a => ofPredicate n L (tri a) hL (ht a))).card=0) :
    6*(Fintype.card α : ℤ)+UpperOpenMathRayResources.coreEndRays n L≤(n : ℤ)*(2*n-5) := by
  have h := certificate_triple_even_defect_charge n L hL hn heven triples tri hi ht
  dsimp only at h
  rw [noOrdinaryCore] at h
  norm_num at h
  nlinarith

#print axioms transverse_charge_count
#print axioms core_base_charge_count
#print axioms certificate_all_line_parity_budget
#print axioms certificate_triple_even_no_ordinary_core_upper
end Kobon.UpperOpenMathOrdinaryGlobalCharge
