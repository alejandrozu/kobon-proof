import Kobon.UpperCoreExtraction
import Kobon.Reindex

/-! The classical simple-arrangement upper bound, with all simplicity and
finite-witness extraction premises discharged from SimpleLowerBound itself.
This does not assert the same upper bound for arbitrary multiple-point or
parallel-line arrangements. -/
namespace Kobon.UpperSimpleOptimality
open Cells FanGeometry UpperVertexBudget UpperCoreExtraction Finset
set_option autoImplicit false

theorem ordinary_intersection (n : Nat) (L : Nat→Line ℝ)
    (hp : NoParallel n L) (hs : NoConcurrent n L)
    (i j : Fin n) (hij : i≠j) : OrdinaryAt n L (intersection (L i) (L j)) := by
  have hd := noParallel_any n L hp i j i.isLt j.isLt
    (fun h => hij (Fin.ext h))
  refine ⟨i,j,hij,?_⟩
  intro r
  constructor
  · intro hr
    by_cases hri : r=i
    · exact Or.inl hri
    by_cases hrj : r=j
    · exact Or.inr hrj
    exfalso
    have hn : evalVertex (L r) (L i) (L j)≠0 := by
      rcases lt_or_gt_of_ne hij with h | h
      · exact BBLTriangles.no_concurrent_at_pair n L hs i j r h hri hrj
      · rw [Reindex.eval_pair_swap]
        exact neg_ne_zero.mpr (BBLTriangles.no_concurrent_at_pair n L hs j i r h hrj hri)
    rw [eval_intersection _ _ _ hd] at hr
    exact (div_ne_zero hn hd) hr
  · rintro (rfl|rfl)
    · exact intersection_on_left _ _ hd
    · exact intersection_on_right _ _ hd

theorem core_empty (n : Nat) (L : Nat→Line ℝ)
    (hp : NoParallel n L) (hs : NoConcurrent n L) : core n L=∅ := by
  classical
  apply eq_empty_iff_forall_notMem.mpr
  intro p hp'
  obtain ⟨hv,hno⟩ := mem_filter.mp hp'
  obtain ⟨⟨i,j⟩,hij,he⟩ := mem_image.mp hv
  rw [← he] at hno
  exact hno (ordinary_intersection n L hp hs i j (mem_offDiag.mp hij).2.2)

/-- Every finite injective certified family in any simple arrangement obeys
the classical segment-count upper bound. The family need not enumerate all cells. -/
theorem certificate_upper {α : Type*} [Fintype α]
    (n : Nat) (L : Nat→Line ℝ) (hp : NoParallel n L) (hs : NoConcurrent n L)
    (hn : 2≤n) (tri : α→Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a)) :
    3*(Fintype.card α : ℤ)≤(n : ℤ)*(n-2) :=
  simple_arrangement_upper n L hp hn tri hi ht (core_empty n L hp hs)

/-- An existential lower-bound certificate cannot exceed the simple upper
bound; the list-to-finite-family map is extracted from its Nodup proof. -/
theorem simple_lower_bound_upper (n T : Nat) (hn : 2≤n)
    (h : SimpleLowerBound n T) : 3*T≤n*(n-2) := by
  obtain ⟨L,hp,hs,ts,hnd,ht,hc⟩ := h
  have hu := certificate_upper n L hp hs hn ts.get hnd.injective_get
    (fun i => ht _ (List.get_mem ts i))
  simp only [Fintype.card_fin] at hu
  have he : ((n*(n-2) : Nat) : ℤ)=(n : ℤ)*(n-2) := by
    simp only [Nat.cast_mul,Nat.cast_sub hn,Nat.cast_ofNat]
  rw [← he] at hu
  have hnat : 3*ts.length≤n*(n-2) := by exact_mod_cast hu
  omega

theorem simple_lower_bound_floor (n T : Nat) (hn : 2≤n)
    (h : SimpleLowerBound n T) : T≤n*(n-2)/3 := by
  have hu := simple_lower_bound_upper n T hn h
  omega

#print axioms core_empty
#print axioms certificate_upper
#print axioms simple_lower_bound_upper
#print axioms simple_lower_bound_floor
end Kobon.UpperSimpleOptimality
