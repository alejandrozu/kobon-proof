import Kobon.OpenMathBoundarySectors
import Kobon.BBLExtrema
import Mathlib.Data.Finset.Sort

/-! Actual projective normal charts extracted from a nonparallel arrangement.
Critical values are exact rational expressions in line coefficients, and their
ordering is the order embedding of the actual finite critical set.
-/
namespace Kobon.OpenMathBoundaryChart
open Exterior OpenMathBoundaryNormals OpenMathBoundarySectors Finset
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem projection_two_zero (l m : Line ℝ) (p : Point) (hd : det l m≠0)
    (hl : projection l p=0) (hm : projection m p=0) : p=(0,0) := by
  have hx : det l m*p.1=m.b*projection l p-l.b*projection m p := by
    dsimp [det,projection]; ring
  have hy : det l m*p.2= -m.a*projection l p+l.a*projection m p := by
    dsimp [det,projection]; ring
  rw [hl,hm,mul_zero,mul_zero,sub_self] at hx
  rw [hl,hm,mul_zero,mul_zero,zero_add] at hy
  apply Prod.ext
  · exact (mul_eq_zero.mp hx).resolve_left hd
  · exact (mul_eq_zero.mp hy).resolve_left hd

theorem projection_nonzero_transverse (l m : Line ℝ) (p : Point) (hd : det l m≠0)
    (hp : p≠(0,0)) (hl : projection l p=0) : projection m p≠0 := by
  intro hm
  exact hp (projection_two_zero l m p hd hl hm)

theorem critical_injective_pair (base l m : Line ℝ) (hb : 0<normSquare base)
    (hl : det l base≠0) (hm : det m base≠0) (hd : det l m≠0) :
    critical base l≠critical base m := by
  intro he
  let w := normalAt base (critical base l)
  have hwl : det l w=0 := normalAt_critical base l hl
  have hwm : det m w=0 := by dsimp [w]; rw [he]; exact normalAt_critical base m hm
  have hd0 : direction w=(0,0) := by
    apply projection_two_zero l m (direction w) hd
    · simpa [direction,projection,det,mul_neg,sub_eq_add_neg] using hwl
    · simpa [direction,projection,det,mul_neg,sub_eq_add_neg] using hwm
  have hwa : w.a=0 := by have h := congrArg Prod.snd hd0; dsimp [direction] at h; linarith
  have hwb : w.b=0 := congrArg Prod.fst hd0
  have hh := base_normalAt base (critical base l)
  change det base w=normSquare base at hh
  simp only [det,hwa,hwb,mul_zero,sub_self] at hh
  linarith

theorem pole_norm_positive (n : Nat) (L : Nat→Line ℝ) (hp : NoParallel n L) (hn : 2≤n) :
    0<normSquare (L 0) := by
  have hd := hp ⟨0,by omega⟩ ⟨1,by omega⟩ (by change (0 : Nat)<1; omega)
  have hs0 : 0≤(L 0).a^2 := sq_nonneg _
  have hs1 : 0≤(L 0).b^2 := sq_nonneg _
  by_contra h
  have hz : (L 0).a=0 ∧ (L 0).b=0 := by dsimp [normSquare] at h; constructor <;> nlinarith
  exact hd (by simp [det,hz.1,hz.2])

def otherIndex (n : Nat) (j : Fin (n-1)) : Fin n := ⟨j.val+1,by have := j.isLt; omega⟩

noncomputable def criticalValues (n : Nat) (L : Nat→Line ℝ) : Finset ℝ := by
  classical
  exact univ.image (fun j : Fin (n-1) => critical (L 0) (L (otherIndex n j)))

theorem criticalValues_card (n : Nat) (L : Nat→Line ℝ) (hp : NoParallel n L) (hn : 2≤n) :
    (criticalValues n L).card=n-1 := by
  classical
  have hi : Function.Injective (fun j : Fin (n-1) => critical (L 0) (L (otherIndex n j))) := by
    intro i j hij
    by_contra hne
    have hindices : otherIndex n i≠otherIndex n j := by
      intro h
      apply hne
      apply Fin.ext
      have hh := congrArg Fin.val h
      dsimp [otherIndex] at hh
      omega
    have h0i : (⟨0,by omega⟩ : Fin n)≠otherIndex n i := by intro h; have := congrArg Fin.val h; dsimp [otherIndex] at this; omega
    have h0j : (⟨0,by omega⟩ : Fin n)≠otherIndex n j := by intro h; have := congrArg Fin.val h; dsimp [otherIndex] at this; omega
    exact critical_injective_pair (L 0) _ _ (pole_norm_positive n L hp hn)
      (BBLExtrema.det_ne_of_ne n L hp (otherIndex n i) ⟨0,by omega⟩ h0i.symm)
      (BBLExtrema.det_ne_of_ne n L hp (otherIndex n j) ⟨0,by omega⟩ h0j.symm)
      (BBLExtrema.det_ne_of_ne n L hp (otherIndex n i) (otherIndex n j) hindices) hij
  unfold criticalValues
  rw [card_image_of_injective _ hi,card_univ,Fintype.card_fin]

noncomputable def roots (n : Nat) (L : Nat→Line ℝ) (hp : NoParallel n L) (hn : 2≤n) :
    Fin (n-1)→ℝ := (criticalValues n L).orderEmbOfFin (criticalValues_card n L hp hn)

theorem roots_strictMono (n : Nat) (L : Nat→Line ℝ) (hp : NoParallel n L) (hn : 2≤n) :
    StrictMono (roots n L hp hn) :=
  ((criticalValues n L).orderEmbOfFin (criticalValues_card n L hp hn)).strictMono

theorem roots_cover (n : Nat) (L : Nat→Line ℝ) (hp : NoParallel n L) (hn : 2≤n)
    (i : Fin n) (hi : i.val≠0) : ∃ j : Fin (n-1), roots n L hp hn j=critical (L 0) (L i) := by
  classical
  let k : Fin (n-1) := ⟨i.val-1,by have := i.isLt; omega⟩
  have hk : otherIndex n k=i := by apply Fin.ext; dsimp [otherIndex,k]; omega
  have hv : critical (L 0) (L i)∈criticalValues n L := by
    apply mem_image.mpr
    exact ⟨k,mem_univ k,by rw [hk]⟩
  obtain ⟨j,hj⟩ := (criticalValues n L).orderIsoOfFin (criticalValues_card n L hp hn) |>.surjective ⟨_,hv⟩
  exact ⟨j,congrArg Subtype.val hj⟩

theorem roots_mem (n : Nat) (L : Nat→Line ℝ) (hp : NoParallel n L) (hn : 2≤n)
    (j : Fin (n-1)) :
    ∃ i : Fin n, i.val≠0 ∧ critical (L 0) (L i)=roots n L hp hn j := by
  classical
  have hv := (criticalValues n L).orderEmbOfFin_mem (criticalValues_card n L hp hn) j
  obtain ⟨k,hk,hv⟩ := mem_image.mp hv
  refine ⟨otherIndex n k,?_,hv⟩
  dsimp [otherIndex]
  omega

#print axioms criticalValues_card
#print axioms roots_strictMono
#print axioms roots_cover
end Kobon.OpenMathBoundaryChart