import Kobon.UpperCoreExtraction
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Core-to-core shared edges versus core-line incidences

On each line, core-to-core elementary edges form a subgraph of a path on the
ordered intersection vertices. Their number is at most the number of core
vertices on that line minus one, when there is a core vertex. Summing gives
`D2 + h <= I` for the actual finite core and actual shared-edge classes.
-/
namespace Kobon.UpperCoreLineIncidence
open Cells FanGeometry UpperVertexBudget UpperTriangleIncidence
  UpperSharedIncidence UpperEdgeInventory UpperCoreExtraction Finset
open scoped BigOperators

/-- A selected set of adjacent path edges uses at least one more selected
vertex whenever the vertex set is nonempty. -/
theorem path_count (m : ℕ) (S : Finset (Fin m)) (F : Finset (Fin (m-1)))
    (left : ∀ k∈F, (⟨k.val,by have := k.isLt; omega⟩ : Fin m)∈S)
    (right : ∀ k∈F, (⟨k.val+1,by have := k.isLt; omega⟩ : Fin m)∈S) :
    F.card+(if S.Nonempty then 1 else 0)≤S.card := by
  classical
  let low : Fin (m-1) → Fin m := fun k => ⟨k.val,by have := k.isLt; omega⟩
  have hinj : Function.Injective low := by
    intro a b he
    apply Fin.ext
    exact congrArg (fun k : Fin m => k.val) he
  by_cases hS : S.Nonempty
  · let last := S.max' hS
    have hsub : F.image low⊆S.erase last := by
      intro x hx
      obtain ⟨k,hk,rfl⟩ := mem_image.mp hx
      refine mem_erase.mpr ⟨?_,left k hk⟩
      have hnext := le_max' S (⟨k.val+1,by have := k.isLt; omega⟩ : Fin m) (right k hk)
      intro he
      have hh := congrArg Fin.val he
      change k.val=last.val at hh
      change k.val+1≤last.val at hnext
      omega
    have hc := card_le_card hsub
    rw [card_image_of_injective _ hinj,card_erase_of_mem (max'_mem S hS)] at hc
    simp only [hS,ite_true]
    have hp := card_pos.mpr hS
    omega
  · have hf : F=∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro k hk
      exact hS ⟨_,left k hk⟩
    simp [hS,hf]

noncomputable def onCoreLine (n : ℕ) (L : ℕ → Line ℝ) (i : Fin n) : Finset Point := by
  classical
  exact (core n L).filter (fun p => affineEval (L i) p=0)

noncomputable def coreLines (n : ℕ) (L : ℕ → Line ℝ) : Finset (Fin n) := by
  classical
  exact univ.filter (fun i => (onCoreLine n L i).Nonempty)

noncomputable def coreIndices (n : ℕ) (L : ℕ → Line ℝ) (i : Fin n) :
    Finset (Fin (coordinates n L i).card) := by
  classical
  exact univ.filter (fun k => orderedPoint n L i k∈core n L)

noncomputable def coreStarts {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (geometry : α → TriangleGeometry) (i : Fin n) :
    Finset (Fin ((coordinates n L i).card-1)) := by
  classical
  exact univ.filter (fun k => intervalEdge n L i k∈twoCoreEdges n L geometry)

theorem coreIndices_card (n : ℕ) (L : ℕ → Line ℝ)
    (hL : NoParallel n L) (hn : 2≤n) (i : Fin n) :
    (coreIndices n L i).card=(onCoreLine n L i).card := by
  classical
  have he : (coreIndices n L i).image (orderedPoint n L i)=onCoreLine n L i := by
    ext p
    constructor
    · intro hp
      obtain ⟨k,hk,rfl⟩ := mem_image.mp hp
      exact mem_filter.mpr ⟨(mem_filter.mp hk).2,
        (mem_filter.mp (orderedPoint_mem n L hL hn i k)).2⟩
    · intro hp
      obtain ⟨hc,hl⟩ := mem_filter.mp hp
      have hv : p∈onLine n L i := mem_filter.mpr ⟨(mem_filter.mp hc).1,hl⟩
      obtain ⟨k,hk⟩ := orderedPoint_surjective n L hL hn i hv
      exact mem_image.mpr ⟨k,mem_filter.mpr ⟨mem_univ k,by rw [hk]; exact hc⟩,hk⟩
  rw [← he,card_image_of_injective _ (orderedPoint_injective n L i)]

theorem core_line_incidence (n : ℕ) (L : ℕ → Line ℝ) :
    (∑ i : Fin n, (onCoreLine n L i).card)=∑ p∈core n L, (supports n L p).card := by
  classical
  simp only [onCoreLine,supports,card_eq_sum_ones,sum_filter]
  exact sum_comm

theorem local_core_path_bound {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (geometry : α → TriangleGeometry) (i : Fin n) :
    (coreStarts n L geometry i).card+
      (if (onCoreLine n L i).Nonempty then 1 else 0)≤(onCoreLine n L i).card := by
  classical
  have hends (k : Fin ((coordinates n L i).card-1)) (hk : k∈coreStarts n L geometry i) :
      (⟨k.val,by have := k.isLt; omega⟩ : Fin (coordinates n L i).card)∈coreIndices n L i ∧
      (⟨k.val+1,by have := k.isLt; omega⟩ : Fin (coordinates n L i).card)∈coreIndices n L i := by
    have htwo := (mem_filter.mp hk).2
    have hordinary := twoCore_endpoints n L geometry htwo
    constructor
    all_goals
      apply mem_filter.mpr
      refine ⟨mem_univ _,mem_filter.mpr ⟨?_,?_⟩⟩
    · exact (mem_filter.mp (orderedPoint_mem n L hL hn i _)).1
    · exact hordinary _ (by simp [intervalEdge])
    · exact (mem_filter.mp (orderedPoint_mem n L hL hn i _)).1
    · exact hordinary _ (by simp [intervalEdge])
  have hh := path_count (coordinates n L i).card (coreIndices n L i)
    (coreStarts n L geometry i) (fun k hk => (hends k hk).1) (fun k hk => (hends k hk).2)
  have hc := coreIndices_card n L hL hn i
  have hnemp : (coreIndices n L i).Nonempty ↔ (onCoreLine n L i).Nonempty := by
    rw [← card_pos,← card_pos,hc]
  simpa only [hnemp,hc] using hh

theorem coreStarts_card {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (geometry : α → TriangleGeometry) (i : Fin n) :
    (coreStarts n L geometry i).card=
      (lineEdges n L i∩twoCoreEdges n L geometry).card := by
  classical
  have he : (coreStarts n L geometry i).image (intervalEdge n L i)=
      lineEdges n L i∩twoCoreEdges n L geometry := by
    ext e
    simp only [coreStarts,lineEdges,mem_image,mem_filter,mem_univ,true_and,mem_inter]
    constructor
    · rintro ⟨k,hk,rfl⟩
      exact ⟨⟨k,rfl⟩,hk⟩
    · rintro ⟨⟨k,rfl⟩,hk⟩
      exact ⟨k,hk,rfl⟩
  rw [← he,card_image_of_injective _ (intervalEdge_injective n L i)]

/-- Fully extracted `D2 + h <= I` for actual certified triangle families.
No incidence or core-edge counting premise is assumed. -/
theorem core_line_budget {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (ht : ∀ a, TrianglePredicate n L (tri a)) :
    let geometry := fun a => ofPredicate n L (tri a) hL (ht a)
    (twoCoreEdges n L geometry).card+(coreLines n L).card≤
      ∑ p∈core n L, (supports n L p).card := by
  classical
  let geometry := fun a => ofPredicate n L (tri a) hL (ht a)
  let D := twoCoreEdges n L geometry
  have hD : D⊆edges n L := by
    intro e he
    exact certificate_sides_subset n L hL hn tri ht (mem_filter.mp (mem_sdiff.mp he).1).1
  have hsplit : D=univ.biUnion (fun i : Fin n => lineEdges n L i∩D) := by
    ext e
    constructor
    · intro he
      obtain ⟨i,_,hi⟩ := mem_biUnion.mp (hD he)
      exact mem_biUnion.mpr ⟨i,mem_univ _,mem_inter.mpr ⟨hi,he⟩⟩
    · intro he
      obtain ⟨i,_,hi⟩ := mem_biUnion.mp he
      exact (mem_inter.mp hi).2
  have hdisj : ((univ : Finset (Fin n)) : Set (Fin n)).PairwiseDisjoint
      (fun i => lineEdges n L i∩D) := by
    intro i hi j hj hij
    exact (lineEdges_pairwise_disjoint n L hL hn hi hj hij).mono inter_subset_left inter_subset_left
  have hcard : D.card=∑ i : Fin n, (coreStarts n L geometry i).card := by
    rw [hsplit,card_biUnion hdisj]
    apply sum_congr rfl
    intro i _
    exact (coreStarts_card n L geometry i).symm
  have hsum := sum_le_sum (s:=univ) (fun i _ => local_core_path_bound n L hL hn geometry i)
  rw [sum_add_distrib,← hcard,core_line_incidence] at hsum
  have hcount : (∑ i : Fin n, (if (onCoreLine n L i).Nonempty then 1 else 0))=
      (coreLines n L).card := by simp [coreLines,sum_boole]
  rw [hcount] at hsum
  exact hsum

#print axioms path_count
#print axioms local_core_path_bound
#print axioms core_line_budget
end Kobon.UpperCoreLineIncidence

