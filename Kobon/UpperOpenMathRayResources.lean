import Kobon.UpperOpenMathCoreCapacity

/-!
# Exact bounded and unbounded resources at multiple points

The first and last actual intersection vertex on each indexed line each
provide one unbounded ray. Counting those whose vertex is a core yields
`Rc`. Unlike a capacity slack, this count is defined from the actual ordered
vertex lists. Every core-line incidence contributes exactly two rays, giving
`D1 + 2*D2 + C + Rc = 2*I`, where `C` counts nonshared bounded endpoints.
-/
namespace Kobon.UpperOpenMathRayResources
open Cells FanGeometry UpperVertexBudget UpperTriangleIncidence UpperSharedIncidence
  UpperEdgeInventory UpperCoreExtraction UpperCoreLineIncidence
  UpperOpenMathCoreCapacity Finset
open scoped BigOperators

noncomputable def endFlags (m : ℕ) (S : Finset (Fin m)) : ℕ := by
  classical
  exact (S.filter (fun k => k.val=0)).card+(S.filter (fun k => k.val+1=m)).card

theorem path_endpoint_exact (m : ℕ) (S : Finset (Fin m)) :
    (∑ k : Fin (m-1), (
      (if (⟨k.val,by have := k.isLt; omega⟩ : Fin m)∈S then 1 else 0)+
      (if (⟨k.val+1,by have := k.isLt; omega⟩ : Fin m)∈S then 1 else 0)))+
      endFlags m S=2*S.card := by
  classical
  let low : Fin (m-1) → Fin m := fun k => ⟨k.val,by have := k.isLt; omega⟩
  let high : Fin (m-1) → Fin m := fun k => ⟨k.val+1,by have := k.isLt; omega⟩
  have ilow : Function.Injective low := by
    intro a b he
    apply Fin.ext
    exact congrArg (fun x : Fin m => x.val) he
  have ihigh : Function.Injective high := by
    intro a b he
    apply Fin.ext
    have hh := congrArg (fun x : Fin m => x.val) he
    dsimp [high] at hh
    omega
  let A := univ.filter (fun k => low k∈S)
  let B := univ.filter (fun k => high k∈S)
  have hA : A.image low=S.filter (fun k => k.val+1<m) := by
    ext x
    constructor
    · intro hx
      obtain ⟨k,hk,rfl⟩ := mem_image.mp hx
      exact mem_filter.mpr ⟨(mem_filter.mp hk).2,by dsimp [low]; have := k.isLt; omega⟩
    · intro hx
      obtain ⟨hxS,hxv⟩ := mem_filter.mp hx
      let k : Fin (m-1) := ⟨x.val,by omega⟩
      have he : low k=x := by apply Fin.ext; rfl
      exact mem_image.mpr ⟨k,mem_filter.mpr ⟨mem_univ _,by rw [he]; exact hxS⟩,he⟩
  have hB : B.image high=S.filter (fun k => 0<k.val) := by
    ext x
    constructor
    · intro hx
      obtain ⟨k,hk,rfl⟩ := mem_image.mp hx
      exact mem_filter.mpr ⟨(mem_filter.mp hk).2,by dsimp [high]; omega⟩
    · intro hx
      obtain ⟨hxS,hxv⟩ := mem_filter.mp hx
      let k : Fin (m-1) := ⟨x.val-1,by have := x.isLt; omega⟩
      have he : high k=x := by apply Fin.ext; dsimp [high,k]; omega
      exact mem_image.mpr ⟨k,mem_filter.mpr ⟨mem_univ _,by rw [he]; exact hxS⟩,he⟩
  have ha := congrArg Finset.card hA
  have hb := congrArg Finset.card hB
  rw [card_image_of_injective _ ilow] at ha
  rw [card_image_of_injective _ ihigh] at hb
  have hlast : S.filter (fun k => ¬ k.val+1<m)=S.filter (fun k => k.val+1=m) := by
    apply filter_congr
    intro k hk
    have := k.isLt
    omega
  have hfirst : S.filter (fun k => ¬ 0<k.val)=S.filter (fun k => k.val=0) := by
    apply filter_congr
    intro k hk
    omega
  have hl := card_filter_add_card_filter_not (s:=S) (fun k : Fin m => k.val+1<m)
  have hf := card_filter_add_card_filter_not (s:=S) (fun k : Fin m => 0<k.val)
  rw [hlast] at hl
  rw [hfirst] at hf
  have hc : (∑ k : Fin (m-1),
      ((if low k∈S then (1 : ℕ) else 0)+(if high k∈S then 1 else 0)))=A.card+B.card := by
    simp [sum_add_distrib,sum_boole,A,B]
  change (∑ k : Fin (m-1),
    ((if low k∈S then 1 else 0)+(if high k∈S then 1 else 0)))+endFlags m S=_
  rw [hc]
  dsimp [endFlags]
  omega

noncomputable def coreEndRays (n : ℕ) (L : ℕ → Line ℝ) : ℕ :=
  ∑ i : Fin n, endFlags (coordinates n L i).card (coreIndices n L i)

theorem line_core_endpoint_exact (n : ℕ) (L : ℕ → Line ℝ)
    (hL : NoParallel n L) (hn : 2≤n) (i : Fin n) :
    (∑ e∈lineEdges n L i, (e∩core n L).card)+
      endFlags (coordinates n L i).card (coreIndices n L i)=2*(onCoreLine n L i).card := by
  classical
  rw [lineEdges,sum_image]
  · simp_rw [interval_core_card]
    have hh := path_endpoint_exact (coordinates n L i).card (coreIndices n L i)
    rw [coreIndices_card n L hL hn i] at hh
    exact hh
  · intro a _ b _ he
    exact intervalEdge_injective n L i he

theorem inventory_core_endpoint_exact (n : ℕ) (L : ℕ → Line ℝ)
    (hL : NoParallel n L) (hn : 2≤n) :
    (∑ e∈edges n L, (e∩core n L).card)+coreEndRays n L=
      2*(∑ p∈core n L, (supports n L p).card) := by
  classical
  rw [edges,sum_biUnion (lineEdges_pairwise_disjoint n L hL hn)]
  have hh := sum_congr (s₁:=univ) rfl (fun i _ => line_core_endpoint_exact n L hL hn i)
  rw [sum_add_distrib,← mul_sum,core_line_incidence] at hh
  exact hh

theorem certificate_ray_resource_identity {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a)) :
    let G := fun a => ofPredicate n L (tri a) hL (ht a)
    (oneCoreEdges n L G).card+2*(twoCoreEdges n L G).card+
      nonsharedCoreIncidences n L G+coreEndRays n L=
        2*(∑ p∈core n L, (supports n L p).card) := by
  classical
  let G := fun a => ofPredicate n L (tri a) hL (ht a)
  have hsub : sharedEdges G⊆edges n L := by
    intro e he
    exact certificate_sides_subset n L hL hn tri ht (mem_filter.mp he).1
  have hsum := sum_sdiff hsub (f:=fun e : Edge => (e∩core n L).card)
  have hid := shared_core_endpoint_count n L hL tri hi ht
  have hex := inventory_core_endpoint_exact n L hL hn
  change (∑ e∈sharedEdges G, (e∩core n L).card)=
    (oneCoreEdges n L G).card+2*(twoCoreEdges n L G).card at hid
  change (oneCoreEdges n L G).card+2*(twoCoreEdges n L G).card+
    (∑ e∈edges n L\sharedEdges G, (e∩core n L).card)+coreEndRays n L=_
  omega

/-- Exact multiple-point defect decomposition, exposing the boundary rays
and every actual bounded endpoint instead of an unspecified capacity loss. -/
theorem certificate_defect_ray_identity {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a)) :
    let G := fun a => ofPredicate n L (tri a) hL (ht a)
    2*((n : ℤ)*(n-2)-3*Fintype.card α)=
      2*(∑ p∈core n L, (supports n L p).card*((supports n L p).card-3 : ℤ))+
      2*(edges n L\usedEdges G).card+nonsharedCoreIncidences n L G+coreEndRays n L-
      (oneCoreEdges n L G).card := by
  classical
  let G := fun a => ofPredicate n L (tri a) hL (ht a)
  have hid := defect_identity n L hL hn tri hi ht
  have hr := certificate_ray_resource_identity n L hL hn tri hi ht
  have hrZ : ((oneCoreEdges n L G).card : ℤ)+2*(twoCoreEdges n L G).card+
      nonsharedCoreIncidences n L G+coreEndRays n L=
      2*(∑ p∈core n L, ((supports n L p).card : ℤ)) := by exact_mod_cast hr
  have hweight : (∑ p∈core n L, (supports n L p).card*((supports n L p).card-2 : ℤ))=
      (∑ p∈core n L, (supports n L p).card*((supports n L p).card-3 : ℤ))+
      ∑ p∈core n L, ((supports n L p).card : ℤ) := by
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro p hp
    ring
  dsimp only at hid
  rw [hweight] at hid
  linarith

#print axioms inventory_core_endpoint_exact
#print axioms certificate_ray_resource_identity
#print axioms certificate_defect_ray_identity
end Kobon.UpperOpenMathRayResources
