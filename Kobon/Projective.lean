import Kobon.Euclidean
import Kobon.Simple
import Mathlib.Tactic

/-! A real projective change of affine chart, with exact sign covariance.
The map on affine points is (x,y) -> (x/(h-x),y/(h-x)).
Choosing h away from all old vertex abscissae gives a nonparallel arrangement.
-/
namespace Kobon.Projective

def transform (h : ℝ) (l : Line ℝ) : Line ℝ :=
  ⟨h*l.a-l.c,h*l.b,l.c⟩

theorem det_transform (h : ℝ) (l m : Line ℝ) :
    det (transform h l) (transform h m) = h*(h*det l m-(vertex l m).1) := by
  simp only [transform,det,vertex]
  ring

theorem eval_transform (h : ℝ) (r l m : Line ℝ) :
    evalVertex (transform h r) (transform h l) (transform h m) =
      h^2*evalVertex r l m := by
  simp only [transform,evalVertex,vertex,det]
  ring

theorem oriented_transform (h : ℝ) (r l m : Line ℝ) (hd : det l m≠0) :
    orientedEval (transform h r) (transform h l) (transform h m) =
      h^3*orientedEval r l m*(h-(intersection l m).1) := by
  rw [orientedEval,eval_transform,det_transform]
  dsimp [orientedEval,intersection]
  field_simp

theorem noParallel_transform (n : ℕ) (L : ℕ → Line ℝ) (h : ℝ)
    (hh : h≠0) (hp : NoParallel n L)
    (hcut : ∀ i j : Fin n, i<j → (intersection (L i) (L j)).1≠h) :
    NoParallel n (fun i => transform h (L i)) := by
  intro i j hij
  rw [det_transform]
  apply mul_ne_zero hh
  intro he
  apply hcut i j hij
  dsimp [intersection]
  exact (div_eq_iff (hp i j hij)).mpr (by linarith)

theorem nonneg_preserved (h : ℝ) (r l m : Line ℝ) (hh : 0<h)
    (hd : det l m≠0) (hc : (intersection l m).1<h)
    (he : 0≤orientedEval r l m) :
    0≤orientedEval (transform h r) (transform h l) (transform h m) := by
  rw [oriented_transform h r l m hd]
  exact mul_nonneg (mul_nonneg (by positivity) he) (sub_nonneg.mpr hc.le)

theorem nonpos_preserved (h : ℝ) (r l m : Line ℝ) (hh : 0<h)
    (hd : det l m≠0) (hc : (intersection l m).1<h)
    (he : orientedEval r l m≤0) :
    orientedEval (transform h r) (transform h l) (transform h m)≤0 := by
  rw [oriented_transform h r l m hd]
  exact mul_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonneg_of_nonpos (by positivity) he) (sub_nonneg.mpr hc.le)

theorem nonneg_flipped (h : ℝ) (r l m : Line ℝ) (hh : 0<h)
    (hd : det l m≠0) (hc : h<(intersection l m).1)
    (he : 0≤orientedEval r l m) :
    orientedEval (transform h r) (transform h l) (transform h m)≤0 := by
  rw [oriented_transform h r l m hd]
  exact mul_nonpos_of_nonneg_of_nonpos
    (mul_nonneg (by positivity) he) (sub_nonpos.mpr hc.le)

theorem factor_pos_negative (h x : ℝ) (hh : h<0) (hx : h<x) :
    0<h^3*(h-x) := by
  have hcube : h^3<0 := by nlinarith [sq_pos_of_ne_zero hh.ne]
  exact mul_pos_of_neg_of_neg hcube (sub_neg.mpr hx)

theorem factor_neg_negative (h x : ℝ) (hh : h<0) (hx : x<h) :
    h^3*(h-x)<0 := by
  have hcube : h^3<0 := by nlinarith [sq_pos_of_ne_zero hh.ne]
  exact mul_neg_of_neg_of_pos hcube (sub_pos.mpr hx)

theorem oriented_transform_factor (h : ℝ) (r l m : Line ℝ) (hd : det l m≠0) :
    orientedEval (transform h r) (transform h l) (transform h m) =
      (h^3*(h-(intersection l m).1))*orientedEval r l m := by
  rw [oriented_transform h r l m hd]
  ring

theorem nonneg_preserved_negative (h : ℝ) (r l m : Line ℝ) (hh : h<0)
    (hd : det l m≠0) (hc : h<(intersection l m).1)
    (he : 0≤orientedEval r l m) :
    0≤orientedEval (transform h r) (transform h l) (transform h m) := by
  rw [oriented_transform_factor h r l m hd]
  exact mul_nonneg (factor_pos_negative h _ hh hc).le he

theorem nonpos_preserved_negative (h : ℝ) (r l m : Line ℝ) (hh : h<0)
    (hd : det l m≠0) (hc : h<(intersection l m).1)
    (he : orientedEval r l m≤0) :
    orientedEval (transform h r) (transform h l) (transform h m)≤0 := by
  rw [oriented_transform_factor h r l m hd]
  exact mul_nonpos_of_nonneg_of_nonpos (factor_pos_negative h _ hh hc).le he

theorem nonneg_flipped_negative (h : ℝ) (r l m : Line ℝ) (hh : h<0)
    (hd : det l m≠0) (hc : (intersection l m).1<h)
    (he : 0≤orientedEval r l m) :
    orientedEval (transform h r) (transform h l) (transform h m)≤0 := by
  rw [oriented_transform_factor h r l m hd]
  exact mul_nonpos_of_nonpos_of_nonneg (factor_neg_negative h _ hh hc).le he

theorem nonpos_flipped_negative (h : ℝ) (r l m : Line ℝ) (hh : h<0)
    (hd : det l m≠0) (hc : (intersection l m).1<h)
    (he : orientedEval r l m≤0) :
    0≤orientedEval (transform h r) (transform h l) (transform h m) := by
  rw [oriented_transform_factor h r l m hd]
  exact mul_nonneg_of_nonpos_of_nonpos (factor_neg_negative h _ hh hc).le he

theorem triangle_preserved (n : ℕ) (L : ℕ → Line ℝ) (h : ℝ)
    (hh : 0<h) (hp : NoParallel n L) (t : Triple)
    (ht : TrianglePredicate n L t)
    (hij : (intersection (L t.i) (L t.j)).1<h)
    (hik : (intersection (L t.i) (L t.k)).1<h)
    (hjk : (intersection (L t.j) (L t.k)).1<h) :
    TrianglePredicate n (fun i => transform h (L i)) t := by
  rcases ht with ⟨h1,h2,h3,hd,hs⟩
  have hi : t.i<n := by omega
  have hj : t.j<n := by omega
  have d1 := hp ⟨t.i,hi⟩ ⟨t.j,hj⟩ h1
  have d2 := hp ⟨t.i,hi⟩ ⟨t.k,h3⟩ (by exact_mod_cast (show t.i<t.k by omega))
  have d3 := hp ⟨t.j,hj⟩ ⟨t.k,h3⟩ h2
  refine ⟨h1,h2,h3,?_,?_⟩
  · rw [eval_transform]
    exact mul_ne_zero (pow_ne_zero _ hh.ne') hd
  · intro r
    rcases hs r with hs | hs
    · left
      exact ⟨nonneg_preserved h _ _ _ hh d1 hij hs.1,
        nonneg_preserved h _ _ _ hh d2 hik hs.2.1,
        nonneg_preserved h _ _ _ hh d3 hjk hs.2.2⟩
    · right
      exact ⟨nonpos_preserved h _ _ _ hh d1 hij hs.1,
        nonpos_preserved h _ _ _ hh d2 hik hs.2.1,
        nonpos_preserved h _ _ _ hh d3 hjk hs.2.2⟩

theorem triangle_preserved_negative (n : ℕ) (L : ℕ → Line ℝ) (h : ℝ)
    (hh : h<0) (hp : NoParallel n L) (t : Triple)
    (ht : TrianglePredicate n L t)
    (hij : h<(intersection (L t.i) (L t.j)).1)
    (hik : h<(intersection (L t.i) (L t.k)).1)
    (hjk : h<(intersection (L t.j) (L t.k)).1) :
    TrianglePredicate n (fun i => transform h (L i)) t := by
  rcases ht with ⟨h1,h2,h3,hd,hs⟩
  have hi : t.i<n := by omega
  have hj : t.j<n := by omega
  have d1 := hp ⟨t.i,hi⟩ ⟨t.j,hj⟩ h1
  have d2 := hp ⟨t.i,hi⟩ ⟨t.k,h3⟩ (by exact_mod_cast (show t.i<t.k by omega))
  have d3 := hp ⟨t.j,hj⟩ ⟨t.k,h3⟩ h2
  refine ⟨h1,h2,h3,?_,?_⟩
  · rw [eval_transform]
    exact mul_ne_zero (pow_ne_zero _ hh.ne) hd
  · intro r
    rcases hs r with hs | hs
    · left
      exact ⟨nonneg_preserved_negative h _ _ _ hh d1 hij hs.1,
        nonneg_preserved_negative h _ _ _ hh d2 hik hs.2.1,
        nonneg_preserved_negative h _ _ _ hh d3 hjk hs.2.2⟩
    · right
      exact ⟨nonpos_preserved_negative h _ _ _ hh d1 hij hs.1,
        nonpos_preserved_negative h _ _ _ hh d2 hik hs.2.1,
        nonpos_preserved_negative h _ _ _ hh d3 hjk hs.2.2⟩

#print axioms triangle_preserved
end Kobon.Projective
