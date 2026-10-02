import Kobon.UpperCleanCover
import Kobon.UpperCoreLineIncidence
import Mathlib.Data.Finset.Sigma

/-!
# Extracted even-order clean-line charging budget

The local clean-line charge is mapped to an actual edge and its ordinary
endpoint. This map is injective: the supporting edge line is unique and the
other line through an ordinary point is unique. Unused edges supply at most
two endpoints, while D1 edges supply exactly one.
-/
namespace Kobon.UpperCleanCharging
open Cells FanGeometry UpperVertexBudget UpperTriangleIncidence
  UpperSharedIncidence UpperEdgeInventory UpperCoreExtraction
  UpperCoreLineIncidence UpperCleanHalfplane UpperCleanCover Finset
open scoped BigOperators

noncomputable def cleanLines (n : ℕ) (L : ℕ → Line ℝ) : Finset (Fin n) := by
  classical
  exact univ.filter (Clean n L)

theorem cleanLines_complement (n : ℕ) (L : ℕ → Line ℝ) :
    cleanLines n L=univ\coreLines n L := by
  classical
  ext i
  simp only [cleanLines,mem_filter,mem_univ,true_and,mem_sdiff]
  constructor
  · intro hc hi
    obtain ⟨p,hp⟩ := (mem_filter.mp hi).2
    obtain ⟨hpc,hpL⟩ := mem_filter.mp hp
    obtain ⟨hpV,hpo⟩ := mem_filter.mp hpc
    exact hpo (hc p (mem_filter.mpr ⟨hpV,hpL⟩))
  · intro hi p hp
    by_contra hpo
    apply hi
    exact mem_filter.mpr ⟨mem_univ _,⟨p,mem_filter.mpr
      ⟨mem_filter.mpr ⟨(mem_filter.mp hp).1,hpo⟩,(mem_filter.mp hp).2⟩⟩⟩

theorem cleanLines_card (n : ℕ) (L : ℕ → Line ℝ) :
    (cleanLines n L).card=n-(coreLines n L).card := by
  classical
  rw [cleanLines_complement,card_sdiff_of_subset (subset_univ _)]
  simp

theorem inventory_card_two
    (n : ℕ) (L : ℕ → Line ℝ) {e : Edge} (he : e∈edges n L) : e.card=2 := by
  classical
  obtain ⟨i,hi,hei⟩ := mem_biUnion.mp he
  obtain ⟨k,hk,rfl⟩ := mem_image.mp hei
  exact intervalEdge_card n L i k

/-- An ordinary endpoint and its actual supporting edge determine the
charging line uniquely. -/
theorem charge_line_unique
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (i j r s : Fin n) (e : Edge) (p : Point)
    (hp : p∈e) (ho : OrdinaryAt n L p)
    (hr : r≠i) (hs : s≠j)
    (her : e∈lineEdges n L r) (hes : e∈lineEdges n L s)
    (hpi : affineEval (L i) p=0) (hpj : affineEval (L j) p=0) : i=j := by
  classical
  have hrs : r=s := by
    by_contra hne
    exact disjoint_left.mp (lineEdges_pairwise_disjoint n L hL hn
      (mem_univ r) (mem_univ s) hne) her hes
  have hpr := edge_endpoints_on_line n L hL hn her p hp
  apply ordinary_nonradial_unique n L p ho r i j hpr hpi hpj hr.symm
  simpa only [hrs] using hs.symm

noncomputable def ordinaryEndpoints (n : ℕ) (L : ℕ → Line ℝ) (e : Edge) : Finset Point := by
  classical
  exact e.filter (OrdinaryAt n L)

theorem oneCore_ordinary_card {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    {e : Edge} (he : e∈oneCoreEdges n L (fun a => ofPredicate n L (tri a) hL (ht a))) :
    (ordinaryEndpoints n L e).card=1 := by
  classical
  unfold ordinaryEndpoints
  obtain ⟨p,q,hpq,rfl,hpo,hqc⟩ := certificate_oneCore_classification n L hL tri hi ht he
  have hqo : ¬OrdinaryAt n L q := (mem_filter.mp hqc).2
  have hf : ({p,q} : Finset Point).filter (OrdinaryAt n L)={p} := by
    ext x
    simp only [mem_filter,mem_insert,mem_singleton]
    constructor
    · rintro ⟨hx,hxo⟩
      rcases hx with rfl|rfl
      · rfl
      · exact False.elim (hqo hxo)
    · rintro rfl
      exact ⟨Or.inl rfl,hpo⟩
  change (({p,q} : Finset Point).filter (OrdinaryAt n L)).card=1
  rw [hf,card_singleton]

/-- Full geometric clean-line parity budget. Every count is extracted from
the real arrangement and the chosen finite injective certificate family. -/
theorem certificate_clean_line_budget {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 3≤n) (heven : n%2=0)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a)) :
    let t := fun a => ofPredicate n L (tri a) hL (ht a)
    n-(coreLines n L).card≤2*(edges n L\usedEdges t).card+(oneCoreEdges n L t).card := by
  classical
  let t := fun a => ofPredicate n L (tri a) hL (ht a)
  let U := edges n L\usedEdges t
  let D := oneCoreEdges n L t
  let B := U∪D
  let C := cleanLines n L
  let β := {i : Fin n // i∈C}
  have hex : ∀ i : β, ∃ e : Edge, ∃ p : Point, ∃ r : Fin n,
      e∈B ∧ p∈e ∧ p∈onLine n L i.val ∧ r≠i.val ∧ e∈lineEdges n L r := by
    intro i
    have hc : Clean n L i.val := (mem_filter.mp i.property).2
    obtain ⟨e,he,p,hpe,hp,r,hr,her⟩ := certificate_clean_line_charge n L hL hn i.val hc heven tri hi ht
    exact ⟨e,p,r,mem_union.mpr he,hpe,hp,hr,her⟩
  choose charge point support hcharge using hex
  let f : β → (Σ _e : Edge, Point) := fun i => ⟨charge i,point i⟩
  have hf : Function.Injective f := by
    intro i j he
    have heq : charge i=charge j := congrArg Sigma.fst he
    have hpq : point i=point j := congrArg (fun z : Σ _e : Edge, Point => z.2) he
    apply Subtype.ext
    have hci : Clean n L i.val := (mem_filter.mp i.property).2
    apply charge_line_unique n L hL (by omega) i.val j.val (support i) (support j)
      (charge i) (point i) (hcharge i).2.1 (hci _ (hcharge i).2.2.1)
      (hcharge i).2.2.2.1 (hcharge j).2.2.2.1 (hcharge i).2.2.2.2
    · simpa only [heq] using (hcharge j).2.2.2.2
    · exact (mem_filter.mp (hcharge i).2.2.1).2
    · simpa only [hpq] using (mem_filter.mp (hcharge j).2.2.1).2
  let target := B.sigma (fun e => e.filter (OrdinaryAt n L))
  have hsub : univ.image f⊆target := by
    intro z hz
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hz
    have hci : Clean n L i.val := (mem_filter.mp i.property).2
    exact mem_sigma.mpr ⟨(hcharge i).1,mem_filter.mpr
      ⟨(hcharge i).2.1,hci _ (hcharge i).2.2.1⟩⟩
  have hcTarget : C.card≤target.card := by
    have hh := card_le_card hsub
    rw [card_image_of_injective _ hf,card_univ] at hh
    simpa only [β,Fintype.card_coe] using hh
  have hUD : Disjoint U D := by
    apply disjoint_left.mpr
    intro e heU heD
    exact (mem_sdiff.mp heU).2 (mem_filter.mp (mem_filter.mp heD).1).1
  have hU : ∀ e∈U, (e.filter (OrdinaryAt n L)).card≤2 := by
    intro e he
    have hh := card_le_card (filter_subset (OrdinaryAt n L) e)
    rw [inventory_card_two n L (mem_sdiff.mp he).1] at hh
    exact hh
  have hD : ∀ e∈D, (e.filter (OrdinaryAt n L)).card=1 :=
    fun e he => oneCore_ordinary_card n L hL tri hi ht he
  have htarget : target.card≤2*U.card+D.card := by
    change (B.sigma (fun e => e.filter (OrdinaryAt n L))).card≤_
    rw [card_sigma]
    change (∑ e∈U∪D, (e.filter (OrdinaryAt n L)).card)≤_
    rw [sum_union hUD]
    have hsU : (∑ e∈U, (e.filter (OrdinaryAt n L)).card)≤2*U.card := by
      calc
        (∑ e∈U, (e.filter (OrdinaryAt n L)).card)≤∑ _e∈U, 2 := sum_le_sum hU
        _=2*U.card := by simp [Nat.mul_comm]
    have hsD : (∑ e∈D, (e.filter (OrdinaryAt n L)).card)=D.card := by
      calc
        (∑ e∈D, (e.filter (OrdinaryAt n L)).card)=∑ _e∈D, 1 := sum_congr rfl hD
        _=D.card := by simp
    rw [hsD]
    exact Nat.add_le_add_right hsU D.card
  have hc : C.card=n-(coreLines n L).card := cleanLines_card n L
  rw [hc] at hcTarget
  exact hcTarget.trans htarget

#print axioms charge_line_unique
#print axioms oneCore_ordinary_card
#print axioms certificate_clean_line_budget
end Kobon.UpperCleanCharging
