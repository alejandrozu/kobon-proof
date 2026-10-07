import Kobon.OpenMathBoundarySuccessor
import Kobon.OpenMathBoundaryIntegerAveraging

/-! A count-only quantitative successor valid for either parity in the simple
model.  All geometric hypotheses are supplied by the old lower-bound witness.
The guaranteed gain is a ceiling average of actual double-terminal vertices;
it is not a claim of the unrestricted half-order recurrence. -/
namespace Kobon.OpenMathQuantitativeSuccessor
open Cells FanGeometry UpperVertexBudget OpenMathSimpleBoundary
  OpenMathBoundaryWitnesses OpenMathBoundarySuccessor
  OpenMathBoundaryIntegerAveraging OpenMathBoundaryDoubleCounting
  Exterior Finset
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 2000000

def deficit (n T : Nat) : Nat := n*(n-2)-3*T
def boundaryLower (n T : Nat) : Nat := n-deficit n T
def gain (n T : Nat) : Nat := ((n-1)*boundaryLower n T+2*n-1)/(2*n)

theorem extension_of_boundary_lower (n T B : Nat) (L : Nat → Line ℝ)
    (hp : NoParallel n L) (hs : NoConcurrent n L) (hn : 2≤n)
    (ts : List Triple) (hnd : ts.Nodup)
    (ht : ∀ t∈ts, TrianglePredicate n L t) (hc : T≤ts.length)
    (hb : B≤(doubleTerminals n L).card) :
    SimpleLowerBound (n+1) (T+((n-1)*B+2*n-1)/(2*n)) := by
  classical
  let β := {p : Point // p∈doubleTerminals n L}
  letI : Fintype β := Finset.Subtype.fintype _
  letI : Nonempty (Fin n × Bool) := ⟨⟨⟨0,by omega⟩,false⟩⟩
  have hbcard : B≤Fintype.card β := by simpa only [β,Fintype.card_coe] using hb
  obtain ⟨a,ha⟩ := exists_ceiling_selected_of_card_bound
    (selected n L hp hn) (n-1) B hbcard
    (boundary_selection_degree n L hp hs hn)
  apply extension_of_selected n T _ L hp hs hn ts hnd ht hc a
  simpa only [Fintype.card_prod,Fintype.card_fin,Fintype.card_bool,Nat.mul_comm n 2] using ha

/-- Both parity cases follow from the actual old geometric certificate.
For n≥3 let δ=n(n−2)−3T and b=max(0,n−δ); the new count is
T+ceil((n−1)b/(2n)). Natural subtraction implements max(0,·). -/
theorem successor (n T : Nat) (hn : 3≤n) (h : SimpleLowerBound n T) :
    SimpleLowerBound (n+1) (T+gain n T) := by
  classical
  have hcap := UpperSimpleOptimality.simple_lower_bound_upper n T (by omega) h
  obtain ⟨L,hp,hs,ts,hnd,ht,hc⟩ := h
  have hb := certificate_boundary_defect n L hp hs hn ts.get
    hnd.injective_get (fun i => ht _ (List.get_mem ts i))
  simp only [Fintype.card_fin] at hb
  have hcount : (T : ℤ)≤ts.length := by exact_mod_cast hc
  have hdefcast : ((deficit n T : Nat) : ℤ)=(n : ℤ)*(n-2)-3*T := by
    unfold deficit
    rw [Nat.cast_sub hcap]
    simp only [Nat.cast_mul,Nat.cast_sub (by omega : 2≤n),Nat.cast_ofNat]
  have hbz : (n : ℤ)-(deficit n T : ℤ)≤(doubleTerminals n L).card := by
    rw [hdefcast]
    linarith
  have hB : boundaryLower n T≤(doubleTerminals n L).card := by
    unfold boundaryLower
    by_cases hd : deficit n T≤n
    · have hcB : ((n-deficit n T : Nat) : ℤ)=(n : ℤ)-(deficit n T : ℤ) := by
        exact Nat.cast_sub hd
      rw [←hcB] at hbz
      exact_mod_cast hbz
    · omega
  exact extension_of_boundary_lower n T (boundaryLower n T) L hp hs (by omega) ts hnd ht hc hB

#print axioms extension_of_boundary_lower
#print axioms successor
end Kobon.OpenMathQuantitativeSuccessor
