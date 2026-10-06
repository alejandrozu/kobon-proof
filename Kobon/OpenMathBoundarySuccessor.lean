import Kobon.OpenMathBoundaryWitnesses
import Kobon.OpenMathBoundarySignedSamples
import Kobon.OpenMathBoundaryDoubleCounting

/-! Quantitative exterior insertion from actual simple arrangements.
The boundary witnesses, finite normal choices, distinct new triples and
preservation of every old triangle are discharged from real line geometry.
The perfect odd special case appears in BBL (2007); the deficit-two case
below also covers the rounded optimal odd orders congruent to one mod six. -/
namespace Kobon.OpenMathBoundarySuccessor
open Cells FanGeometry UpperVertexBudget OpenMathSimpleBoundary
  OpenMathBoundaryNormals OpenMathBoundarySectorGeometry
  OpenMathBoundarySignedSamples OpenMathBoundaryWitnesses
  OpenMathBoundaryDoubleCounting Exterior Finset
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 2000000

noncomputable def selected (n : Nat) (L : Nat → Line ℝ)
    (hp : NoParallel n L) (hn : 2≤n)
    (a : Fin n × Bool) (v : {p : Point // p∈doubleTerminals n L}) : Prop :=
  0<projection (normal n L hp hn a) (witness n L hp hn v).first ∧
  0<projection (normal n L hp hn a) (witness n L hp hn v).second

theorem boundary_selection_degree (n : Nat) (L : Nat → Line ℝ)
    (hp : NoParallel n L) (hs : NoConcurrent n L) (hn : 2≤n)
    (v : {p : Point // p∈doubleTerminals n L}) :
    selectedCount (fun v a => selected n L hp hn a v) v=n-1 := by
  classical
  rw [selectedCount,Finset.card_filter]
  have he : (∑ a : Fin n × Bool, if selected n L hp hn a v then (1 : Nat) else 0)=
      ∑ a : Fin n × Bool, if 0<projection (normal n L hp hn a) (witness n L hp hn v).first ∧
        0<projection (normal n L hp hn a) (witness n L hp hn v).second then (1 : Nat) else 0 := by
    apply sum_congr rfl
    intro a ha
    unfold selected
    split_ifs <;> rfl
  rw [he]
  exact pair_signed_sector_count n L hp hn
    (witness n L hp hn v).i (witness n L hp hn v).j
    (witness n L hp hn v).ordered
    (witness n L hp hn v).first (witness n L hp hn v).second
    (witness n L hp hn v).first_ne (witness n L hp hn v).second_ne
    (witness n L hp hn v).first_tangent (witness n L hp hn v).second_tangent
    ((witness n L hp hn v).compatible hp hs)

theorem selected_visible_list (n : Nat) (L : Nat → Line ℝ)
    (hp : NoParallel n L) (hs : NoConcurrent n L) (hn : 2≤n)
    (a : Fin n × Bool) :
    ∃ ns : List Triple, ns.Nodup ∧
      (∀ t∈ns, VisiblePair n L (normal n L hp hn a) t) ∧
      ns.length=selectedCount (selected n L hp hn) a := by
  classical
  let S := univ.filter (selected n L hp hn a)
  let f := fun v : {p : Point // p∈doubleTerminals n L} => (witness n L hp hn v).triple
  refine ⟨S.toList.map f,S.nodup_toList.map (witness_triple_injective n L hp hn),?_,?_⟩
  · intro t ht
    obtain ⟨v,hv,rfl⟩ := List.mem_map.mp ht
    have hvS : v∈S := mem_toList.mp hv
    have hsel := (mem_filter.mp hvS).2
    exact (witness n L hp hn v).visible hp hs _ (normal_admissible n L hp hn a)
      hsel.1 hsel.2
  · simp only [List.length_map,length_toList]
    rfl

/-- Any selected normal realizes every selected boundary vertex and preserves
the supplied old triangle list in one actual simple arrangement. -/
theorem extension_of_selected (n T g : Nat) (L : Nat → Line ℝ)
    (hp : NoParallel n L) (hs : NoConcurrent n L) (hn : 2≤n)
    (ts : List Triple) (hnd : ts.Nodup)
    (ht : ∀ t∈ts, TrianglePredicate n L t) (hc : T≤ts.length)
    (a : Fin n × Bool) (hg : g≤selectedCount (selected n L hp hn) a) :
    SimpleLowerBound (n+1) (T+g) := by
  obtain ⟨ns,hns,hvis,hcard⟩ := selected_visible_list n L hp hs hn a
  have he := Exterior.extension n T L ts ns (normal n L hp hn a)
    (safeHeight n L (normal n L hp hn a)) hp hs hnd ht hc hns hvis
    (normal_admissible n L hp hn a) (safeHeight_beyond n L _)
  apply he.mono
  omega

/-- The extra hypothesis is solely the triangle count in the old simple
arrangement. No exterior direction, boundary count or future triangle is
assumed. Perfect odd arrangements are the BBL 2007 special case. -/
theorem odd_defect_two_successor (m T : Nat) (hm : 1≤m)
    (h : SimpleLowerBound (2*m+1) T)
    (hdef : ((2*m+1 : Nat) : ℤ)*(2*m-1)-3*T≤2) :
    SimpleLowerBound (2*m+2) (T+m) := by
  classical
  obtain ⟨L,hp,hs,ts,hnd,ht,hc⟩ := h
  have hn : 3≤2*m+1 := by omega
  have hb := certificate_boundary_defect (2*m+1) L hp hs hn ts.get
    hnd.injective_get (fun i => ht _ (List.get_mem ts i))
  simp only [Fintype.card_fin] at hb
  have hcount : (T : ℤ)≤ts.length := by exact_mod_cast hc
  have hB : 2*m-1≤(doubleTerminals (2*m+1) L).card := by
    have hBz : (2*m-1 : ℤ)≤(doubleTerminals (2*m+1) L).card := by
      norm_num at hb hdef ⊢
      linarith
    have hcast : ((2*m-1 : Nat) : ℤ)=2*(m : ℤ)-1 := by
      rw [Nat.cast_sub (by omega : 1≤2*m)]
      simp
    rw [←hcast] at hBz
    exact_mod_cast hBz
  have hcard : Fintype.card (Fin (2*m+1) × Bool)=4*m+2 := by simp; omega
  let B := doubleTerminals (2*m+1) L
  let β := {p : Point // p∈B}
  letI : Fintype β := Finset.Subtype.fintype B
  have hvertices : 2*m-1≤Fintype.card β := by
    simpa only [β,B,Fintype.card_coe] using hB
  obtain ⟨a,ha⟩ := exists_half_gain_of_degree m hm hcard hvertices
    (selected (2*m+1) L hp (by omega)) (fun v => by
      simpa using boundary_selection_degree (2*m+1) L hp hs (by omega) v)
  have he := extension_of_selected (2*m+1) T m L hp hs (by omega) ts hnd ht hc a ha
  convert he using 1 <;> omega

#print axioms boundary_selection_degree
#print axioms selected_visible_list
#print axioms extension_of_selected
#print axioms odd_defect_two_successor
end Kobon.OpenMathBoundarySuccessor
