import Kobon.OpenMathBoundaryChart
import Kobon.OpenMathBoundaryRootOrder

/-! Exact sector averaging for an actual pair of terminal supporting rays.
The compatibility premise is the sign invariant of the two geometric rays,
proved from actual terminal vertices in OpenMathBoundaryRays. All critical
values and all sample normals are extracted from the given arrangement.
-/
namespace Kobon.OpenMathBoundarySectorGeometry
open Exterior OpenMathBoundaryNormals OpenMathBoundarySectors OpenMathBoundaryChart
open OpenMathBoundarySampleExistence OpenMathBoundaryRootOrder Finset
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 2000000

noncomputable def samples (n : Nat) (L : Nat→Line ℝ) (hp : NoParallel n L) (hn : 2≤n) :
    Samples n := sectorSamples hn (roots n L hp hn) (roots_strictMono n L hp hn)

@[simp] theorem samples_roots (n : Nat) (L : Nat→Line ℝ) (hp : NoParallel n L) (hn : 2≤n) :
    (samples n L hp hn).roots=roots n L hp hn := rfl

 theorem sample_ne_root (n : Nat) (D : Samples n) (k : Fin n) (i : Fin (n-1)) :
    D.sample k≠D.roots i := by
  by_cases h : i.val<k.val
  · exact ne_of_gt ((D.left k i).mpr h)
  · exact ne_of_lt ((D.right k i).mpr (by omega))

 theorem sample_admissible (n : Nat) (L : Nat→Line ℝ) (hp : NoParallel n L) (hn : 2≤n)
    (k : Fin n) : Admissible n L (normalAt (L 0) ((samples n L hp hn).sample k)) := by
  intro i
  by_cases hi : i.val=0
  · have hv : (i : Nat)=0 := hi
    simpa [hv,base_normalAt] using ne_of_gt (pole_norm_positive n L hp hn)
  · obtain ⟨j,hj⟩ := roots_cover n L hp hn i hi
    have h0i : i≠(⟨0,by omega⟩ : Fin n) := by intro hh; exact hi (congrArg Fin.val hh)
    have hd := BBLExtrema.det_ne_of_ne n L hp i ⟨0,by omega⟩ h0i
    intro hz
    have he : (samples n L hp hn).sample k=critical (L 0) (L i) := by
      rw [normalAt_determinant] at hz
      unfold critical
      apply (eq_div_iff hd).mpr
      linarith
    exact sample_ne_root n (samples n L hp hn) k j (by simpa only [samples_roots,hj] using he)

 theorem choiceCount_comm (a b : ℝ) : choiceCount a b=choiceCount b a := by
  rw [choiceCount_product,choiceCount_product,mul_comm]

 theorem projection_norm_base_zero (base : Line ℝ) (p : Point) (h : projection base p=0)
    (s : ℝ) : projection (normalAt base s) p=projection (rotatedNormal base) p := by
  rw [normalAt_projection,h,mul_zero,add_zero]

 theorem pair_sector_count (n : Nat) (L : Nat→Line ℝ) (hp : NoParallel n L) (hn : 2≤n)
    (i j : Fin n) (hij : i<j) (p q : Point) (hpn : p≠(0,0)) (hqn : q≠(0,0))
    (hpi : projection (L i) p=0) (hqj : projection (L j) q=0)
    (hc : ∀ r : Fin n, r≠i → r≠j → 0<projection (L r) p*projection (L r) q) :
    (∑ k : Fin n, choiceCount
      (projection (normalAt (L 0) ((samples n L hp hn).sample k)) p)
      (projection (normalAt (L 0) ((samples n L hp hn).sample k)) q))=n-1 := by
  let D := samples n L hp hn
  have hnorm := pole_norm_positive n L hp hn
  have hijne : i≠j := ne_of_lt hij
  have hj0 : j.val≠0 := by have := i.isLt; change i.val<j.val at hij; omega
  have hjpole : j≠(⟨0,by omega⟩ : Fin n) := by intro he; exact hj0 (congrArg Fin.val he)
  have hdj := BBLExtrema.det_ne_of_ne n L hp j ⟨0,by omega⟩ hjpole
  obtain ⟨rj,hrj⟩ := roots_cover n L hp hn j hj0
  change D.roots rj=critical (L 0) (L j) at hrj
  have hfq (s : ℝ) : projection (normalAt (L 0) s) q=
      projection (L 0) q*(s-D.roots rj) := by
    rw [projection_factor (L 0) (L j) q hdj hqj]
    rw [hrj]
    ring
  by_cases hi0 : i.val=0
  · have hi : (i : Nat)=0 := hi0
    have hppole : projection (L 0) p=0 := by simpa only [hi] using hpi
    have hfp (s : ℝ) : projection (normalAt (L 0) s) p=projection (rotatedNormal (L 0)) p :=
      projection_norm_base_zero _ _ hppole s
    let a := projection (rotatedNormal (L 0)) p
    let b := projection (L 0) q
    have ha : a≠0 := by
      apply projection_nonzero_transverse (L 0) (rotatedNormal (L 0)) p _ hpn hppole
      simpa [base_normalAt,normalAt,rotatedNormal,normSquare,det,pow_two] using ne_of_gt hnorm
    have hb : b≠0 := projection_nonzero_transverse (L j) (L 0) q hdj hqn hqj
    have hother (r : Fin (n-1)) (hr : r≠rj) : 0<a*b*(D.roots r-D.roots rj) := by
      obtain ⟨l,hl0,hlr⟩ := roots_mem n L hp hn r
      change critical (L 0) (L l)=D.roots r at hlr
      have hli : l≠i := by intro he; apply hl0; simpa only [he] using hi0
      have hlj : l≠j := by
        intro he
        apply hr
        apply (roots_strictMono n L hp hn).injective
        change D.roots r=D.roots rj
        rw [hrj]
        simpa only [he] using hlr.symm
      have hlpole : l≠(⟨0,by omega⟩ : Fin n) := by intro he; exact hl0 (congrArg Fin.val he)
      have hdl := BBLExtrema.det_ne_of_ne n L hp l ⟨0,by omega⟩ hlpole
      have hh := critical_projection_positive (L 0) (L l) p q hnorm hdl (hc l hli hlj)
      rw [hfp,hfq] at hh
      have he : critical (L 0) (L l)=D.roots r := hlr
      rw [he] at hh
      dsimp [a,b]
      nlinarith
    simp_rw [hfp,hfq]
    rcases lt_or_gt_of_ne (mul_ne_zero ha hb) with hab|hab
    · have hlast : rj.val+1=n-1 := by
        apply last_of_no_larger D.roots (roots_strictMono n L hp hn) rj
        intro r hlt
        have hr : r≠rj := ne_of_gt ((roots_strictMono n L hp hn).lt_iff_lt.mp hlt)
        have hh := hother r hr
        have hnprod := mul_neg_of_neg_of_pos hab (sub_pos.mpr hlt)
        linarith
      have hrjlast : rj=(⟨n-2,by omega⟩ : Fin (n-1)) := by apply Fin.ext; change rj.val=n-2; omega
      rw [hrjlast]
      exact last_root_count n D (by omega) a b hab
    · have hfirst : rj.val=0 := by
        apply first_of_no_smaller D.roots (roots_strictMono n L hp hn) rj
        intro r hlt
        have hr : r≠rj := ne_of_lt ((roots_strictMono n L hp hn).lt_iff_lt.mp hlt)
        have hh := hother r hr
        have hnprod := mul_neg_of_pos_of_neg hab (sub_neg.mpr hlt)
        linarith
      have hrjfirst : rj=(⟨0,by omega⟩ : Fin (n-1)) := Fin.ext hfirst
      rw [hrjfirst]
      exact first_root_count n D (by omega) a b hab
  · have hipole : i≠(⟨0,by omega⟩ : Fin n) := by intro he; exact hi0 (congrArg Fin.val he)
    have hdi := BBLExtrema.det_ne_of_ne n L hp i ⟨0,by omega⟩ hipole
    obtain ⟨ri,hri⟩ := roots_cover n L hp hn i hi0
    change D.roots ri=critical (L 0) (L i) at hri
    have hfp (s : ℝ) : projection (normalAt (L 0) s) p=
        projection (L 0) p*(s-D.roots ri) := by
      rw [projection_factor (L 0) (L i) p hdi hpi]
      rw [hri]
      ring
    have hbase : 0<projection (L 0) p*projection (L 0) q :=
      hc ⟨0,by omega⟩ hipole.symm hjpole.symm
    have hneq : D.roots ri≠D.roots rj := by
      rw [hri,hrj]
      exact critical_injective_pair (L 0) (L i) (L j) hnorm hdi hdj (hp i j hij)
    have hgap (r : Fin (n-1)) :
        ¬(D.roots ri<D.roots r ∧ D.roots r<D.roots rj) ∧
        ¬(D.roots rj<D.roots r ∧ D.roots r<D.roots ri) := by
      obtain ⟨l,hl0,hlr⟩ := roots_mem n L hp hn r
      change critical (L 0) (L l)=D.roots r at hlr
      by_cases hli : l=i
      · simp only [hli] at hlr
        rw [←hlr]
        constructor <;> intro h <;> linarith [h.1,h.2]
      by_cases hlj : l=j
      · simp only [hlj] at hlr
        rw [←hlr]
        constructor <;> intro h <;> linarith [h.1,h.2]
      have hlpole : l≠(⟨0,by omega⟩ : Fin n) := by intro he; exact hl0 (congrArg Fin.val he)
      have hdl := BBLExtrema.det_ne_of_ne n L hp l ⟨0,by omega⟩ hlpole
      have hb := critical_not_between (L 0) (L i) (L j) (L l) p q hnorm hdi hdj hdl hpi hqj hbase (hc l hli hlj)
      have hb' := critical_not_between (L 0) (L j) (L i) (L l) q p hnorm hdj hdi hdl hqj hpi
        (by simpa only [mul_comm] using hbase) (by simpa only [mul_comm] using hc l hli hlj)
      simpa only [hri.symm,hrj.symm,hlr] using And.intro hb hb'
    simp_rw [hfp,hfq]
    rcases lt_or_gt_of_ne hneq with hirj|hjri
    · have hadj := adjacent_of_no_between D.roots (roots_strictMono n L hp hn) ri rj hirj (fun r => (hgap r).1)
      exact adjacent_sector_count n D ri rj hadj _ _ hbase
    · have hadj := adjacent_of_no_between D.roots (roots_strictMono n L hp hn) rj ri hjri (fun r => (hgap r).2)
      simp_rw [choiceCount_comm]
      exact adjacent_sector_count n D rj ri hadj _ _ (by simpa only [mul_comm] using hbase)

#print axioms sample_admissible
#print axioms pair_sector_count
end Kobon.OpenMathBoundarySectorGeometry


