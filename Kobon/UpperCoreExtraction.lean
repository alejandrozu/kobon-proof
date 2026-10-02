import Kobon.UpperEdgeInventory

/-!
# Actual multiple-point core and the extracted defect identity

Ordinary points are exactly vertices incident to two indexed lines. The
multiplicity loss therefore restricts to the actual finite multiple-point
core. The resulting defect identity contains no assumed incidence formula.
The final simple-arrangement upper bound is classical; it is included as a
complete geometric check of the extraction pipeline, not a novelty claim.
-/
namespace Kobon.UpperCoreExtraction
open Cells FanGeometry UpperVertexBudget UpperTriangleIncidence
  UpperSharedIncidence UpperEdgeInventory Finset
open scoped BigOperators

theorem ordinary_iff_support_card (n : ℕ) (L : ℕ → Line ℝ) (p : Point) :
    OrdinaryAt n L p ↔ (supports n L p).card=2 := by
  classical
  constructor
  · rintro ⟨a,b,hab,hinc⟩
    have hs : supports n L p={a,b} := by
      ext i
      simp only [supports,mem_filter,mem_univ,true_and,mem_insert,mem_singleton]
      exact hinc i
    rw [hs]
    exact card_pair hab
  · intro hc
    obtain ⟨a,b,hab,hs⟩ := card_eq_two.mp hc
    refine ⟨a,b,hab,?_⟩
    intro i
    have hh : i∈supports n L p ↔ i=a ∨ i=b := by rw [hs]; simp
    simpa only [supports,mem_filter,mem_univ,true_and] using hh

noncomputable def core (n : ℕ) (L : ℕ → Line ℝ) : Finset Point := by
  classical
  exact (vertices n L).filter (fun p => ¬OrdinaryAt n L p)

theorem core_multiplicity (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L)
    {p : Point} (hp : p∈core n L) : 3≤(supports n L p).card := by
  classical
  obtain ⟨hv,ho⟩ := mem_filter.mp hp
  have htwo := support_card_at_least_two n L hL hv
  have hne : (supports n L p).card≠2 := fun he => ho ((ordinary_iff_support_card n L p).mpr he)
  omega

theorem loss_eq_core_loss (n : ℕ) (L : ℕ → Line ℝ) :
    (∑ p∈vertices n L, (supports n L p).card*((supports n L p).card-2 : ℤ))=
      ∑ p∈core n L, (supports n L p).card*((supports n L p).card-2 : ℤ) := by
  classical
  rw [core,sum_filter]
  apply sum_congr rfl
  intro p _
  by_cases ho : OrdinaryAt n L p
  · have hc := (ordinary_iff_support_card n L p).mp ho
    simp [ho,hc]
  · simp [ho]

/-- Fully extracted defect identity, with the loss summed only over actual
multiple points and the edge classes taken from actual triangle sides. -/
theorem defect_identity {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a)) :
    let geometry := fun a => ofPredicate n L (tri a) hL (ht a)
    (n : ℤ)*(n-2)-3*Fintype.card α=
      (∑ p∈core n L, (supports n L p).card*((supports n L p).card-2 : ℤ))+
      (edges n L\usedEdges geometry).card-
      (oneCoreEdges n L geometry).card-(twoCoreEdges n L geometry).card := by
  have h := certificate_defect_identity n L hL hn tri hi ht
  rw [loss_eq_core_loss] at h
  exact h

/-- The D1 class has exactly one ordinary endpoint and one actual core
endpoint for a certified triangle family, not merely a formal filter label. -/
theorem certificate_oneCore_classification {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    {e : Edge}
    (he : e∈oneCoreEdges n L (fun a => ofPredicate n L (tri a) hL (ht a))) :
    ∃ p q : Point, p≠q ∧ e={p,q} ∧ OrdinaryAt n L p ∧ q∈core n L := by
  classical
  let geometry := fun a => ofPredicate n L (tri a) hL (ht a)
  have hd : Pairwise (fun a b => Disjoint (geometry a).interior (geometry b).interior) := by
    intro a b hab
    exact distinct_interiors_disjoint n L _ _ hL (ht a) (ht b) (fun he => hab (hi he))
  obtain ⟨⟨p,hp,hpo⟩,⟨q,hq,hqn⟩⟩ := oneCore_has_both_kinds n L geometry hL
    (fun a => predicate_indexed n L (tri a) hL (ht a)) hd he
  have hpq : p≠q := by intro h; exact hqn (h ▸ hpo)
  have hused := (mem_filter.mp (mem_filter.mp he).1).1
  have hsub : {p,q}⊆e := by intro x hx; simp only [mem_insert,mem_singleton] at hx; rcases hx with rfl|rfl <;> assumption
  have hpair : {p,q}=e := eq_of_subset_of_card_le hsub (by rw [used_edge_card _ hused,card_pair hpq])
  exact ⟨p,q,hpq,hpair.symm,hpo,mem_filter.mpr
    ⟨certificate_side_vertices n L hL tri ht hused hq,hqn⟩⟩

/-- Classical bound for a pairwise nonparallel arrangement with no multiple
vertices, proved here from the actual geometric extraction. -/
theorem simple_arrangement_upper {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a)) (hcore : core n L=∅) :
    3*(Fintype.card α : ℤ)≤(n : ℤ)*(n-2) := by
  classical
  let geometry := fun a => ofPredicate n L (tri a) hL (ht a)
  have hd : Pairwise (fun a b => Disjoint (geometry a).interior (geometry b).interior) := by
    intro a b hab
    exact distinct_interiors_disjoint n L _ _ hL (ht a) (ht b) (fun he => hab (hi he))
  have hshared : sharedEdges geometry=∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro e he
    obtain ⟨p,hp,hno⟩ := shared_has_nonordinary_endpoint n L geometry hL
      (fun a => predicate_indexed n L (tri a) hL (ht a)) hd he
    have hv := certificate_side_vertices n L hL tri ht (mem_filter.mp he).1 hp
    have hc : p∈core n L := mem_filter.mpr ⟨hv,hno⟩
    rw [hcore] at hc
    exact notMem_empty p hc
  have hi' := exact_incidence geometry hd
  rw [hshared,card_empty,add_zero] at hi'
  have hle := card_le_card (certificate_sides_subset n L hL hn tri ht)
  have he := edge_cardinality n L hL hn
  rw [loss_eq_core_loss,hcore,sum_empty,sub_zero] at he
  have hint : (3*Fintype.card α : ℕ)≤(edges n L).card := hi'.trans_le hle
  have hh : (3 : ℤ)*Fintype.card α≤((edges n L).card : ℤ) := by exact_mod_cast hint
  linarith

#print axioms ordinary_iff_support_card
#print axioms core_multiplicity
#print axioms defect_identity
#print axioms certificate_oneCore_classification
#print axioms simple_arrangement_upper
end Kobon.UpperCoreExtraction

