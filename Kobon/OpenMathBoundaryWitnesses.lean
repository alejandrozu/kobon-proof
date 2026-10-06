import Kobon.OpenMathBoundaryVisibility

/-! Actual double-terminal vertices supply two ordered supporting lines and
two compatible forward rays.  The resulting old-pair descriptors are
injective in the geometric vertex; no visibility count is assumed. -/
namespace Kobon.OpenMathBoundaryWitnesses
open Cells FanGeometry UpperVertexBudget OpenMathSimpleBoundary
  OpenMathBoundaryNormals OpenMathBoundaryRays OpenMathBoundaryVisibility
  Exterior Finset
set_option autoImplicit false
set_option maxHeartbeats 1000000

structure Witness (n : Nat) (L : Nat → Line ℝ) (v : Point) where
  i : Fin n
  j : Fin n
  ordered : i<j
  vertex : intersection (L i) (L j)=v
  first : Point
  second : Point
  first_ne : first≠(0,0)
  second_ne : second≠(0,0)
  first_tangent : projection (L i) first=0
  second_tangent : projection (L j) second=0
  first_signs : TerminalSigns n L v first
  second_signs : TerminalSigns n L v second

theorem ordered_terminal_pair (n : Nat) (L : Nat → Line ℝ)
    {v : Point} (hv : v∈doubleTerminals n L) :
    ∃ i j : Fin n, i<j ∧ v∈lineTerminals n L i ∧ v∈lineTerminals n L j := by
  classical
  obtain ⟨i,j,hij,he⟩ := card_eq_two.mp (mem_filter.mp hv).2
  have hi : v∈lineTerminals n L i := by
    have hm : i∈terminalsAt n L v := by rw [he]; simp
    exact (mem_filter.mp hm).2
  have hj : v∈lineTerminals n L j := by
    have hm : j∈terminalsAt n L v := by rw [he]; simp
    exact (mem_filter.mp hm).2
  rcases lt_or_gt_of_ne hij with h|h
  · exact ⟨i,j,h,hi,hj⟩
  · exact ⟨j,i,h,hj,hi⟩

theorem exists_witness (n : Nat) (L : Nat → Line ℝ)
    (hp : NoParallel n L) (hn : 2≤n)
    {v : Point} (hv : v∈doubleTerminals n L) : Nonempty (Witness n L v) := by
  classical
  obtain ⟨i,j,hij,hi,hj⟩ := ordered_terminal_pair n L hv
  have hpi := terminal_mem_onLine n L hp hn i hi
  have hpj := terminal_mem_onLine n L hp hn j hj
  have he : intersection (L i) (L j)=v :=
    (intersection_eq_iff n L hp i j (ne_of_lt hij) v).mpr
      ⟨(mem_filter.mp hpi).2,(mem_filter.mp hpj).2⟩
  obtain ⟨d,hd,hdi,havoid,hsign⟩ := terminal_outward_signs n L hp hn i hi
  obtain ⟨e,he0,hej,eavoid,esign⟩ := terminal_outward_signs n L hp hn j hj
  exact ⟨⟨i,j,hij,he,d,e,hd,he0,hdi,hej,hsign,esign⟩⟩

noncomputable def witness (n : Nat) (L : Nat → Line ℝ)
    (hp : NoParallel n L) (hn : 2≤n)
    (v : {p : Point // p∈doubleTerminals n L}) : Witness n L v :=
  Classical.choice (exists_witness n L hp hn v.property)

def Witness.triple {n : Nat} {L : Nat → Line ℝ} {v : Point}
    (W : Witness n L v) : Triple := ⟨W.i.val,W.j.val,n⟩

theorem Witness.transverse_eval {n : Nat} {L : Nat → Line ℝ} {v : Point}
    (W : Witness n L v) (hp : NoParallel n L) (hs : NoConcurrent n L)
    (r : Fin n) (hri : r≠W.i) (hrj : r≠W.j) : affineEval (L r) v≠0 := by
  rw [← W.vertex,eval_intersection _ _ _ (hp W.i W.j W.ordered)]
  exact div_ne_zero
    (BBLTriangles.no_concurrent_at_pair n L hs W.i W.j r W.ordered hri hrj)
    (hp W.i W.j W.ordered)

theorem Witness.compatible {n : Nat} {L : Nat → Line ℝ} {v : Point}
    (W : Witness n L v) (hp : NoParallel n L) (hs : NoConcurrent n L)
    (r : Fin n) (hri : r≠W.i) (hrj : r≠W.j) :
    0<projection (L r) W.first*projection (L r) W.second :=
  compatible_directions n L v W.first W.second W.first_signs W.second_signs r
    (W.transverse_eval hp hs r hri hrj)

theorem Witness.visible {n : Nat} {L : Nat → Line ℝ} {v : Point}
    (W : Witness n L v) (hp : NoParallel n L) (hs : NoConcurrent n L)
    (w : Line ℝ) (hw : Admissible n L w)
    (hd : 0<projection w W.first) (he : 0<projection w W.second) :
    VisiblePair n L w W.triple := by
  apply pair_visible_of_terminal_signs n L hp hs W.i W.j W.ordered w hw
    W.first W.second W.first_tangent W.second_tangent
  · simpa only [W.vertex] using W.first_signs
  · simpa only [W.vertex] using W.second_signs
  · exact hd
  · exact he

theorem witness_triple_injective (n : Nat) (L : Nat → Line ℝ)
    (hp : NoParallel n L) (hn : 2≤n) :
    Function.Injective (fun v : {p : Point // p∈doubleTerminals n L} =>
      (witness n L hp hn v).triple) := by
  intro v u he
  have hi : (witness n L hp hn v).i=(witness n L hp hn u).i :=
    Fin.ext (congrArg Triple.i he)
  have hj : (witness n L hp hn v).j=(witness n L hp hn u).j :=
    Fin.ext (congrArg Triple.j he)
  apply Subtype.ext
  rw [← (witness n L hp hn v).vertex,← (witness n L hp hn u).vertex,hi,hj]

#print axioms exists_witness
#print axioms Witness.compatible
#print axioms Witness.visible
#print axioms witness_triple_injective
end Kobon.OpenMathBoundaryWitnesses
