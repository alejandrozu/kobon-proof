import Kobon.HybridBoundary

/-! Real geometric extremal-intersection lemmas used in BBL boundary induction.

The hypotheses concern positions of actual pairwise intersections. They do not
assume triangle counts or the sign certificate that the theorem concludes.
-/
namespace Kobon.BBLExtrema
open Exterior HybridBoundary

theorem det_ne_of_ne (n : Nat) (L : Nat → Line ℝ) (hp : NoParallel n L)
    (i j : Fin n) (hij : i ≠ j) : det (L i) (L j) ≠ 0 := by
  rcases lt_or_gt_of_ne hij with h | h
  · exact hp i j h
  · rw [det_skew]
    exact neg_ne_zero.mpr (hp j i h)

/-- Affine values are directional derivatives times the distance, in the chosen
projection coordinate, from the zero on the same supporting line. -/
theorem evaluation_from_intersection (r l m w : Line ℝ)
    (hlm : det l m ≠ 0) (hlr : det l r ≠ 0) (hwl : det w l ≠ 0) :
    affineEval r (intersection l m) = derivative r l w *
      (projection w (intersection l m)-projection w (intersection l r)) := by
  have hlp := intersection_on_left l m hlm
  have hlq := intersection_on_left l r hlr
  have hrq := intersection_on_right l r hlr
  unfold derivative
  rw [div_mul_eq_mul_div]
  apply (eq_div_iff hwl).mpr
  dsimp only [affineEval,projection,det] at hlp hlq hrq ⊢
  linear_combination (r.b*w.a-r.a*w.b)*hlp -
    (r.b*w.a-r.a*w.b)*hlq + (w.a*l.b-w.b*l.a)*hrq

def StrictExtremalPair (n : Nat) (L : Nat → Line ℝ) (w : Line ℝ) (i j : Nat) : Prop :=
  ∀ r : Fin n, r.val ≠ i → r.val ≠ j →
    projection w (intersection (L i) (L r)) < projection w (intersection (L i) (L j)) ∧
    projection w (intersection (L j) (L r)) < projection w (intersection (L i) (L j))

theorem extremal_visible (n : Nat) (L : Nat → Line ℝ) (w : Line ℝ)
    (hp : NoParallel n L) (hw : Admissible n L w) (t : Triple)
    (hij : t.i<t.j) (hjn : t.j<n) (hkn : t.k=n)
    (he : StrictExtremalPair n L w t.i t.j) : VisiblePair n L w t := by
  have hin : t.i<n := by omega
  have hdet := hp ⟨t.i,hin⟩ ⟨t.j,hjn⟩ hij
  have hdets : det (L t.j) (L t.i) ≠ 0 := by
    rw [det_skew]
    exact neg_ne_zero.mpr hdet
  have hwi : det w (L t.i) ≠ 0 := by
    rw [det_skew]
    exact neg_ne_zero.mpr (hw ⟨t.i,hin⟩)
  have hwj : det w (L t.j) ≠ 0 := by
    rw [det_skew]
    exact neg_ne_zero.mpr (hw ⟨t.j,hjn⟩)
  refine ⟨hij,hjn,hkn,?_⟩
  intro r
  by_cases hri : r.val=t.i
  · simp only [hri,intersection_on_left _ _ hdet]
    have hz : derivative (L t.i) (L t.i) w=0 := by simp [derivative,det,mul_comm]
    rw [hz]
    rcases le_total 0 (derivative (L t.i) (L t.j) w) with h | h
    · exact Or.inl ⟨le_rfl,le_rfl,h⟩
    · exact Or.inr ⟨le_rfl,le_rfl,h⟩
  by_cases hrj : r.val=t.j
  · simp only [hrj,intersection_on_right _ _ hdet]
    have hz : derivative (L t.j) (L t.j) w=0 := by simp [derivative,det,mul_comm]
    rw [hz]
    rcases le_total 0 (derivative (L t.j) (L t.i) w) with h | h
    · exact Or.inl ⟨le_rfl,h,le_rfl⟩
    · exact Or.inr ⟨le_rfl,h,le_rfl⟩
  have hir : det (L t.i) (L r) ≠ 0 := det_ne_of_ne n L hp ⟨t.i,hin⟩ r (by
    intro h
    have hh := congrArg Fin.val h
    exact hri hh.symm)
  have hjr : det (L t.j) (L r) ≠ 0 := det_ne_of_ne n L hp ⟨t.j,hjn⟩ r (by
    intro h
    have hh := congrArg Fin.val h
    exact hrj hh.symm)
  obtain ⟨hei,hej⟩ := he r hri hrj
  have eqi := evaluation_from_intersection (L r) (L t.i) (L t.j) w hdet hir hwi
  have eqj := evaluation_from_intersection (L r) (L t.j) (L t.i) w hdets hjr hwj
  rw [← intersection_swap (L t.i) (L t.j)] at eqj
  have di : 0 < projection w (intersection (L t.i) (L t.j))-
      projection w (intersection (L t.i) (L r)) := sub_pos.mpr hei
  have dj : 0 < projection w (intersection (L t.i) (L t.j))-
      projection w (intersection (L t.j) (L r)) := sub_pos.mpr hej
  rcases le_total 0 (affineEval (L r) (intersection (L t.i) (L t.j))) with ha | ha
  · left
    refine ⟨ha,?_,?_⟩
    · by_contra hn
      have hneg := mul_neg_of_neg_of_pos (lt_of_not_ge hn) di
      linarith [eqi]
    · by_contra hn
      have hneg := mul_neg_of_neg_of_pos (lt_of_not_ge hn) dj
      linarith [eqj]
  · right
    refine ⟨ha,?_,?_⟩
    · by_contra hn
      have hpos := mul_pos (lt_of_not_ge hn) di
      linarith [eqi]
    · by_contra hn
      have hpos := mul_pos (lt_of_not_ge hn) dj
      linarith [eqj]

/-- A finite extension preserves an old extremal pair if every newly introduced
intersection on its two sides lies strictly behind its old vertex. -/
theorem extremal_preserved (n k : Nat) (L L' : Nat → Line ℝ) (w : Line ℝ)
    (i j : Nat) (hi : i<n) (hj : j<n)
    (hold : ∀ r<n, L' r=L r) (he : StrictExtremalPair n L w i j)
    (hnew : ∀ r : Fin (n+k), n≤r.val →
      projection w (intersection (L i) (L' r)) < projection w (intersection (L i) (L j)) ∧
      projection w (intersection (L j) (L' r)) < projection w (intersection (L i) (L j))) :
    StrictExtremalPair (n+k) L' w i j := by
  intro r hri hrj
  rw [hold i hi,hold j hj]
  by_cases hr : r.val<n
  · rw [hold r.val hr]
    exact he ⟨r.val,hr⟩ hri hrj
  · exact hnew r (by omega)

/-- Visibility forces every other crossing on either supporting line to lie
behind the wedge vertex. Concurrent crossings may give equality. -/
theorem visible_extremal (n : Nat) (L : Nat → Line ℝ) (w : Line ℝ)
    (hp : NoParallel n L) (hw : Admissible n L w) (t : Triple)
    (hv : VisiblePair n L w t) (r : Fin n) (hri : r.val ≠ t.i) :
    projection w (intersection (L t.i) (L r)) ≤
      projection w (intersection (L t.i) (L t.j)) := by
  obtain ⟨hij,hjn,hkn,hv⟩ := hv
  have hin : t.i<n := by omega
  have hlm := hp ⟨t.i,hin⟩ ⟨t.j,hjn⟩ hij
  have hlr := det_ne_of_ne n L hp ⟨t.i,hin⟩ r (by
    intro hh
    exact hri (congrArg Fin.val hh).symm)
  have hwl : det w (L t.i) ≠ 0 := by
    rw [det_skew]
    exact neg_ne_zero.mpr (hw ⟨t.i,hin⟩)
  have hrl : det (L r) (L t.i) ≠ 0 := by
    rw [det_skew]
    exact neg_ne_zero.mpr hlr
  have hd : derivative (L r) (L t.i) w ≠ 0 := div_ne_zero hrl hwl
  have heq := evaluation_from_intersection (L r) (L t.i) (L t.j) w hlm hlr hwl
  rcases hv r with ⟨ha,hb,hc⟩ | ⟨ha,hb,hc⟩
  · have hp' : 0<derivative (L r) (L t.i) w := lt_of_le_of_ne hb (Ne.symm hd)
    by_contra hn
    have hg : projection w (intersection (L t.i) (L t.j))-
        projection w (intersection (L t.i) (L r))<0 := by linarith
    have hm := mul_neg_of_pos_of_neg hp' hg
    linarith
  · have hp' : derivative (L r) (L t.i) w<0 := lt_of_le_of_ne hb hd
    by_contra hn
    have hg : projection w (intersection (L t.i) (L t.j))-
        projection w (intersection (L t.i) (L r))<0 := by linarith
    have hm := mul_pos_of_neg_of_neg hp' hg
    linarith

theorem visible_extremal_right (n : Nat) (L : Nat → Line ℝ) (w : Line ℝ)
    (hp : NoParallel n L) (hw : Admissible n L w) (t : Triple)
    (hv : VisiblePair n L w t) (r : Fin n) (hrj : r.val ≠ t.j) :
    projection w (intersection (L t.j) (L r)) ≤
      projection w (intersection (L t.i) (L t.j)) := by
  obtain ⟨hij,hjn,hkn,hv⟩ := hv
  have hin : t.i<n := by omega
  have hlm : det (L t.j) (L t.i) ≠ 0 := by
    rw [det_skew]
    exact neg_ne_zero.mpr (hp ⟨t.i,hin⟩ ⟨t.j,hjn⟩ hij)
  have hlr := det_ne_of_ne n L hp ⟨t.j,hjn⟩ r (by
    intro hh
    exact hrj (congrArg Fin.val hh).symm)
  have hwl : det w (L t.j) ≠ 0 := by
    rw [det_skew]
    exact neg_ne_zero.mpr (hw ⟨t.j,hjn⟩)
  have hrl : det (L r) (L t.j) ≠ 0 := by
    rw [det_skew]
    exact neg_ne_zero.mpr hlr
  have hd : derivative (L r) (L t.j) w ≠ 0 := div_ne_zero hrl hwl
  have heq := evaluation_from_intersection (L r) (L t.j) (L t.i) w hlm hlr hwl
  rw [← intersection_swap (L t.i) (L t.j)] at heq
  rcases hv r with ⟨ha,hb,hc⟩ | ⟨ha,hb,hc⟩
  · have hp' : 0<derivative (L r) (L t.j) w := lt_of_le_of_ne hc (Ne.symm hd)
    by_contra hn
    have hg : projection w (intersection (L t.i) (L t.j))-
        projection w (intersection (L t.j) (L r))<0 := by linarith
    have hm := mul_neg_of_pos_of_neg hp' hg
    linarith
  · have hp' : derivative (L r) (L t.j) w<0 := lt_of_le_of_ne hc hd
    by_contra hn
    have hg : projection w (intersection (L t.i) (L t.j))-
        projection w (intersection (L t.j) (L r))<0 := by linarith
    have hm := mul_pos_of_neg_of_neg hp' hg
    linarith

def graphLine (m a : ℝ) : Line ℝ := ⟨m,-1,m*a⟩

/-- For a graph line with a positive projected rightward direction, order in
the projection is exactly order in the ordinary x-coordinate. -/
theorem graph_projection_order (m a : ℝ) (w : Line ℝ) (p q : Point)
    (hp : affineEval (graphLine m a) p=0) (hq : affineEval (graphLine m a) q=0)
    (hw : 0<w.a+w.b*m) (h : projection w p≤projection w q) : p.1≤q.1 := by
  have heq : projection w q-projection w p=(w.a+w.b*m)*(q.1-p.1) := by
    dsimp only [affineEval,graphLine,projection] at hp hq ⊢
    linear_combination w.b*hp-w.b*hq
  by_contra hn
  have hm := mul_neg_of_pos_of_neg hw (show q.1-p.1<0 by linarith)
  linarith

#print axioms extremal_visible
#print axioms extremal_preserved
#print axioms visible_extremal_right
end Kobon.BBLExtrema
