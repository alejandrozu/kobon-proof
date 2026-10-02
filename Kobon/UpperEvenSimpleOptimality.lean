import Kobon.UpperSimpleOptimality
import Kobon.UpperCleanCharging

/-! The sharper classical even-order simple-arrangement upper bound, derived
from actual clean-line charging and the geometric defect identity. No aggregate
incidence or charging inequality is assumed in the final theorem. -/
namespace Kobon.UpperEvenSimpleOptimality
open Cells FanGeometry UpperVertexBudget UpperCoreExtraction UpperTriangleIncidence
  UpperSharedIncidence UpperEdgeInventory UpperCoreLineIncidence Finset
set_option autoImplicit false

theorem shared_empty {α : Type*} [Fintype α]
    (n : Nat) (L : Nat→Line ℝ) (hp : NoParallel n L) (hs : NoConcurrent n L)
    (tri : α→Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a)) :
    sharedEdges (fun a => ofPredicate n L (tri a) hp (ht a))=∅ := by
  classical
  let geometry := fun a => ofPredicate n L (tri a) hp (ht a)
  have hd : Pairwise (fun a b => Disjoint (geometry a).interior (geometry b).interior) := by
    intro a b hab
    exact distinct_interiors_disjoint n L _ _ hp (ht a) (ht b) (fun he => hab (hi he))
  apply eq_empty_iff_forall_notMem.mpr
  intro e he
  obtain ⟨p,hpe,hno⟩ := shared_has_nonordinary_endpoint n L geometry hp
    (fun a => predicate_indexed n L (tri a) hp (ht a)) hd he
  have hv := certificate_side_vertices n L hp tri ht (mem_filter.mp he).1 hpe
  have hc : p∈core n L := mem_filter.mpr ⟨hv,hno⟩
  rw [UpperSimpleOptimality.core_empty n L hp hs] at hc
  exact notMem_empty p hc

theorem certificate_even_upper {α : Type*} [Fintype α]
    (n : Nat) (L : Nat→Line ℝ) (hp : NoParallel n L) (hs : NoConcurrent n L)
    (hn : 4≤n) (heven : n%2=0) (tri : α→Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a)) :
    6*(Fintype.card α : ℤ)≤(n : ℤ)*(2*n-5) := by
  classical
  let geometry := fun a => ofPredicate n L (tri a) hp (ht a)
  have hcore := UpperSimpleOptimality.core_empty n L hp hs
  have hshared := shared_empty n L hp hs tri hi ht
  have hlines : coreLines n L=∅ := by
    simp [coreLines,onCoreLine,hcore]
  have hcharge := UpperCleanCharging.certificate_clean_line_budget n L hp (by omega)
    heven tri hi ht
  have hcharge' : n≤2*(edges n L\usedEdges geometry).card := by
    simpa only [hlines,card_empty,Nat.sub_zero,oneCoreEdges,hshared,filter_empty,
      Nat.add_zero] using hcharge
  have hchargeZ : (n : ℤ)≤2*((edges n L\usedEdges geometry).card : ℤ) := by
    exact_mod_cast hcharge'
  have hid := UpperCoreExtraction.defect_identity n L hp (by omega) tri hi ht
  have hid' : (n : ℤ)*(n-2)-3*Fintype.card α=
      ((edges n L\usedEdges geometry).card : ℤ) := by
    simpa only [hcore,sum_empty,zero_add,oneCoreEdges,twoCoreEdges,hshared,
      filter_empty,sdiff_empty,card_empty,Nat.cast_zero,sub_zero] using hid
  nlinarith

theorem simple_lower_bound_even_upper (n T : Nat) (hn : 4≤n)
    (heven : n%2=0) (h : SimpleLowerBound n T) : 6*T≤n*(2*n-5) := by
  obtain ⟨L,hp,hs,ts,hnd,ht,hc⟩ := h
  have hu := certificate_even_upper n L hp hs hn heven ts.get hnd.injective_get
    (fun i => ht _ (List.get_mem ts i))
  simp only [Fintype.card_fin] at hu
  have hn' : 5≤2*n := by omega
  have he : ((n*(2*n-5) : Nat) : ℤ)=(n : ℤ)*(2*n-5) := by
    simp only [Nat.cast_mul,Nat.cast_sub hn',Nat.cast_ofNat]
  rw [← he] at hu
  have hnat : 6*ts.length≤n*(2*n-5) := by exact_mod_cast hu
  omega

theorem simple_lower_bound_even_floor (n T : Nat) (hn : 4≤n)
    (heven : n%2=0) (h : SimpleLowerBound n T) : T≤n*(2*n-5)/6 := by
  have hu := simple_lower_bound_even_upper n T hn heven h
  omega

#print axioms certificate_even_upper
#print axioms simple_lower_bound_even_floor
end Kobon.UpperEvenSimpleOptimality
