import Kobon.UpperOpenMathAntipodalFullNeighborPair
import Kobon.UpperFanSupport

namespace Kobon.UpperOpenMathN13SupportScratch
open Cells FanGeometry UpperFan UpperVertexBudget
  UpperOpenMathAntipodalAdjacency
  UpperOpenMathAntipodalBalancedAdjacency Finset
set_option maxHeartbeats 1000000

theorem weak_product_left (l : Line ℝ) (p q r : Point)
    (h : WeakSide l p q r) : 0≤affineEval l p*affineEval l q := by
  rcases h with ⟨hp,hq,hr⟩|⟨hp,hq,hr⟩
  · exact mul_nonneg hp hq
  · exact mul_nonneg_of_nonpos_of_nonpos hp hq

theorem weak_product_right (l : Line ℝ) (p q r : Point)
    (h : WeakSide l p q r) : 0≤affineEval l p*affineEval l r := by
  rcases h with ⟨hp,hq,hr⟩|⟨hp,hq,hr⟩
  · exact mul_nonneg hp hr
  · exact mul_nonneg_of_nonpos_of_nonpos hp hr

/-- At an actual shared triple tip, the two selected cap lines are distinct.
    Empty-cell weak-side tests are essential; arbitrary geometric sectors
    would not suffice. -/
theorem selected_core_cap_ne {n : ℕ} {L : ℕ → Line ℝ}
    (hL : NoParallel n L) (f : Sectors n 3 L) (z : ZMod 6)
    (hm : z-1∈f.triangular) (hz : z∈f.triangular)
    (posM : 0<areaDet f.center (f.point (z-1)) (f.point z))
    (posZ : 0<areaDet f.center (f.point z) (f.point (z+1)))
    (nc : f.point z≠f.center) (inj : Function.Injective f.point)
    (triple : (supports n L (f.point z)).card=3)
    (weakM : ∀ i : Fin n, WeakSide (L i) f.center (f.point (z-1)) (f.point z))
    (weakZ : ∀ i : Fin n, WeakSide (L i) f.center (f.point z) (f.point (z+1))) :
    f.opposite (z-1)≠f.opposite z := by
  classical
  intro he
  have capM := cap_left_at f (z-1) hm
  have capZ := cap_left_at f z hz
  have capP := cap_right_at f z hz
  have capC := cap_avoids_at f z hz
  have col : areaDet (f.point (z-1)) (f.point z) (f.point (z+1))=0 := by
    apply UpperFanSupport.collinear_of_incident_line (L (f.opposite z)) f.center
    · exact capC
    · rw [←he]; exact capM
    · exact capZ
    · exact capP
  have members : supports n L (f.point z)⊆{f.radial z,f.opposite z} := by
    intro i hi
    have iq : affineEval (L i) (f.point z)=0 := (mem_filter.mp hi).2
    by_cases ic : affineEval (L i) f.center=0
    · have ir : i=f.radial z := support_eq_of_two_points n L hL _ _
        f.center (f.point z) nc.symm ic iq (f.radial_center z) (f.radial_point z)
      simp [ir]
    · have hsum := UpperFanSupport.affine_area_identity (L i) f.center
        (f.point (z-1)) (f.point z) (f.point (z+1))
      rw [iq,col] at hsum
      simp only [sub_zero,zero_mul] at hsum
      have hprodM := weak_product_left (L i) _ _ _ (weakM i)
      have hprodZ := weak_product_right (L i) _ _ _ (weakZ i)
      have hnonM : 0≤areaDet f.center (f.point z) (f.point (z+1))*
          (affineEval (L i) f.center*affineEval (L i) (f.point (z-1))) :=
        mul_nonneg posZ.le hprodM
      have hnonZ : 0≤areaDet f.center (f.point (z-1)) (f.point z)*
          (affineEval (L i) f.center*affineEval (L i) (f.point (z+1))) :=
        mul_nonneg posM.le hprodZ
      have hp : affineEval (L i) f.center*affineEval (L i) (f.point (z-1))=0 := by
        have hz := congrArg (fun x : ℝ=>affineEval (L i) f.center*x) hsum
        have hzero : areaDet f.center (f.point z) (f.point (z+1))*
            (affineEval (L i) f.center*affineEval (L i) (f.point (z-1)))=0 := by
          nlinarith [hz]
        exact (mul_eq_zero.mp hzero).resolve_left posZ.ne'
      have ip : affineEval (L i) (f.point (z-1))=0 :=
        (mul_eq_zero.mp hp).resolve_left ic
      have ineq : f.point (z-1)≠f.point z := by
        intro eq
        have h := inj eq
        have zn : z-1≠z := by
          intro h
          exact (by decide : (1 : ZMod 6)≠0) (sub_eq_self.mp h)
        exact zn h
      have it : i=f.opposite z := support_eq_of_two_points n L hL _ _
        (f.point (z-1)) (f.point z) ineq ip iq
        (by rw [←he]; exact capM) capZ
      simp [it]
  have le := card_le_card members
  have le2 : ({f.radial z,f.opposite z} : Finset (Fin n)).card≤2 := by
    exact card_insert_le _ _ |>.trans (by simp)
  rw [triple] at le
  omega

theorem certificate_selected_core_cap_ne {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L)
    (tri : α → Triple) (ht : ∀ a, TrianglePredicate n L (tri a))
    (f : Sectors n 3 L)
    (df : UpperOpenMathAntipodalFullNeighborPair.AnyChartData
      (fun a=>ofPredicate n L (tri a) hL (ht a)) f)
    (z : ZMod 6) (hm : z-1∈f.triangular) (hz : z∈f.triangular)
    (triple : (supports n L (f.point z)).card=3) :
    f.opposite (z-1)≠f.opposite z := by
  have weakAt (w : ZMod 6) (hw : w∈f.triangular) (i : Fin n) :
      WeakSide (L i) f.center (f.point w) (f.point (w+1)) := by
    obtain ⟨o⟩ := df.occurrences w hw
    have he := o.transport.weak (L i)
      (weakSide_of_predicate n L (tri o.index) hL (ht o.index) i)
    simpa only [o.center,o.left,o.right] using he
  exact selected_core_cap_ne hL f z hm hz
    (by simpa only [sub_add_cancel] using df.positive (z-1)) (df.positive z)
    (df.noncentral z) df.injective triple
    (by intro i; simpa only [sub_add_cancel] using weakAt (z-1) hm i) (weakAt z hz)

#print axioms certificate_selected_core_cap_ne
#print axioms selected_core_cap_ne
end Kobon.UpperOpenMathN13SupportScratch



