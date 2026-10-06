import Kobon.UpperOpenMathDegreeBudgets

/-! Maximum degree in the actual simple shared-core graph, extracted
directly from its two-element endpoint sets. -/
namespace Kobon.UpperOpenMathCoreDegree
open Cells FanGeometry UpperVertexBudget UpperTriangleIncidence
  UpperSharedIncidence UpperCoreExtraction UpperCoreCombinatorics
  UpperOpenMathGlobalFans Finset
set_option autoImplicit false

theorem pair_inventory_degree_bound {β : Type*} [DecidableEq β] (P : Finset β)
    (E : Finset (Finset β))
    (pairs : ∀ e∈E, e.card=2 ∧ e⊆P)
    (p : β) (hp : p∈P) :
    (E.filter (fun e => p∈e)).card≤P.card-1 := by
  classical
  let F := E.filter (fun e => p∈e)
  have hsub : F.image (fun e => e.erase p)⊆(P.erase p).powersetCard 1 := by
    intro e he
    obtain ⟨a,ha,rfl⟩ := mem_image.mp he
    obtain ⟨haE,hpa⟩ := mem_filter.mp ha
    obtain ⟨hac,haP⟩ := pairs a haE
    apply mem_powersetCard.mpr
    constructor
    · intro x hx
      obtain ⟨hxp,hxa⟩ := mem_erase.mp hx
      exact mem_erase.mpr ⟨hxp,haP hxa⟩
    · rw [card_erase_of_mem hpa,hac]
  have hinj : Set.InjOn (fun e : Finset β => e.erase p) F := by
    intro a ha b hb he
    have hpa := (mem_filter.mp ha).2
    have hpb := (mem_filter.mp hb).2
    calc
      a=insert p (a.erase p) := (insert_erase hpa).symm
      _=insert p (b.erase p) := congrArg (insert p) he
      _=b := insert_erase hpb
  have hc := card_le_card hsub
  rw [card_image_of_injOn hinj,card_powersetCard,card_erase_of_mem hp] at hc
  simpa only [Nat.choose_one_right] using hc

theorem certificate_core_degree_bound {α : Type*} [Fintype α]
    (n : Nat) (L : Nat→Line ℝ) (hL : NoParallel n L)
    (tri : α→Triple) (ht : ∀ a, TrianglePredicate n L (tri a))
    (p : Point) (hp : p∈core n L) :
    twoDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) p≤
      (core n L).card-1 := by
  classical
  apply pair_inventory_degree_bound
  · intro e he
    have hs := core_edge_subset n L hL tri ht he
    exact ⟨(mem_powersetCard.mp hs).2,(mem_powersetCard.mp hs).1⟩
  · exact hp

theorem certificate_three_core_degree {α : Type*} [Fintype α]
    (n : Nat) (L : Nat→Line ℝ) (hL : NoParallel n L)
    (tri : α→Triple) (ht : ∀ a, TrianglePredicate n L (tri a))
    (small : (core n L).card≤3) :
    ∀ p∈core n L,
      twoDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) p≤2 := by
  intro p hp
  have hh := certificate_core_degree_bound n L hL tri ht p hp
  omega

#print axioms certificate_core_degree_bound
#print axioms certificate_three_core_degree
end Kobon.UpperOpenMathCoreDegree
