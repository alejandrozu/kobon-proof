import Kobon.BBLExtrema

/-! Empty-triangle soundness from two consecutive intersection sides.
This reduces BBL geometry to explicit orders on the added lines.
-/
namespace Kobon.BBLTriangles
open Exterior HybridBoundary BBLExtrema

theorem eval_cyclic (r l m : Line ℝ) : evalVertex r l m=evalVertex m r l := by
  dsimp [evalVertex,vertex,det]
  ring

theorem eval_outer_swap (r l m : Line ℝ) : evalVertex r l m= -evalVertex m l r := by
  dsimp [evalVertex,vertex,det]
  ring

theorem no_concurrent_at_pair (n : Nat) (L : Nat → Line ℝ)
    (hs : NoConcurrent n L) (i j r : Fin n) (hij : i<j)
    (hri : r ≠ i) (hrj : r ≠ j) : evalVertex (L r) (L i) (L j) ≠ 0 := by
  rcases lt_or_gt_of_ne hri with hi | hi
  · rw [eval_cyclic]
    exact hs r i j hi hij
  · rcases lt_or_gt_of_ne hrj with hj | hj
    · rw [eval_outer_swap]
      exact neg_ne_zero.mpr (hs i r j hi hj)
    · exact hs i j r hij hj

def Outside (p a b : ℝ) : Prop := (p≤a ∧ p≤b) ∨ (a≤p ∧ b≤p)

theorem outside_product (p a b : ℝ) (h : Outside p a b) :
    0≤(a-p)*(b-p) := by
  rcases h with ⟨ha,hb⟩ | ⟨ha,hb⟩
  · exact mul_nonneg (sub_nonneg.mpr ha) (sub_nonneg.mpr hb)
  · exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr ha) (sub_nonpos.mpr hb)

theorem outside_evaluation_product (r l m s w : Line ℝ)
    (hlm : det l m ≠ 0) (hls : det l s ≠ 0) (hlr : det l r ≠ 0)
    (hwl : det w l ≠ 0)
    (hout : Outside (projection w (intersection l r))
      (projection w (intersection l m)) (projection w (intersection l s))) :
    0≤affineEval r (intersection l m)*affineEval r (intersection l s) := by
  rw [evaluation_from_intersection r l m w hlm hlr hwl,
    evaluation_from_intersection r l s w hls hlr hwl]
  have hh := mul_nonneg (sq_nonneg (derivative r l w))
    (outside_product _ _ _ hout)
  nlinarith only [hh]

theorem three_signs (x y z : ℝ) (hx : x ≠ 0) (hxy : 0≤x*y) (hxz : 0≤x*z) :
    (0≤x ∧ 0≤y ∧ 0≤z) ∨ (x≤0 ∧ y≤0 ∧ z≤0) := by
  rcases lt_or_gt_of_ne hx with hx | hx
  · right
    refine ⟨le_of_lt hx,?_,?_⟩
    · by_contra hy
      have hh := mul_neg_of_neg_of_pos hx (lt_of_not_ge hy)
      linarith
    · by_contra hz
      have hh := mul_neg_of_neg_of_pos hx (lt_of_not_ge hz)
      linarith
  · left
    refine ⟨le_of_lt hx,?_,?_⟩
    · by_contra hy
      have hh := mul_neg_of_pos_of_neg hx (lt_of_not_ge hy)
      linarith
    · by_contra hz
      have hh := mul_neg_of_pos_of_neg hx (lt_of_not_ge hz)
      linarith

/-- If the two sides meeting at one vertex contain no intervening crossings,
the supporting triple is an actual empty triangle in a simple arrangement.
No separate crossing-order check is needed on its third side. -/
theorem triangle_of_two_sides (n : Nat) (L : Nat → Line ℝ) (w : Line ℝ)
    (hp : NoParallel n L) (hs : NoConcurrent n L) (hw : Admissible n L w)
    (t : Triple) (hij : t.i<t.j) (hjk : t.j<t.k) (hkn : t.k<n)
    (hi : ∀ r : Fin n, r.val ≠ t.i → Outside
      (projection w (intersection (L t.i) (L r)))
      (projection w (intersection (L t.i) (L t.j)))
      (projection w (intersection (L t.i) (L t.k))))
    (hj : ∀ r : Fin n, r.val ≠ t.j → Outside
      (projection w (intersection (L t.j) (L r)))
      (projection w (intersection (L t.i) (L t.j)))
      (projection w (intersection (L t.j) (L t.k)))) : TrianglePredicate n L t := by
  have hin : t.i<n := by omega
  have hjn : t.j<n := by omega
  have hijp := hp ⟨t.i,hin⟩ ⟨t.j,hjn⟩ hij
  have hikp := hp ⟨t.i,hin⟩ ⟨t.k,hkn⟩ (show t.i<t.k from lt_trans hij hjk)
  have hjkp := hp ⟨t.j,hjn⟩ ⟨t.k,hkn⟩ hjk
  have hjip : det (L t.j) (L t.i) ≠ 0 := by
    rw [det_skew]
    exact neg_ne_zero.mpr hijp
  have hwi : det w (L t.i) ≠ 0 := by
    rw [det_skew]
    exact neg_ne_zero.mpr (hw ⟨t.i,hin⟩)
  have hwj : det w (L t.j) ≠ 0 := by
    rw [det_skew]
    exact neg_ne_zero.mpr (hw ⟨t.j,hjn⟩)
  refine ⟨hij,hjk,hkn,hs ⟨t.i,hin⟩ ⟨t.j,hjn⟩ ⟨t.k,hkn⟩ hij hjk,?_⟩
  intro r
  rw [oriented_nonneg_iff _ _ _ hijp,oriented_nonneg_iff _ _ _ hikp,
    oriented_nonneg_iff _ _ _ hjkp,oriented_nonpos_iff _ _ _ hijp,
    oriented_nonpos_iff _ _ _ hikp,oriented_nonpos_iff _ _ _ hjkp]
  by_cases hri : r.val=t.i
  · rw [hri,intersection_on_left _ _ hijp,intersection_on_left _ _ hikp]
    rcases le_total 0 (affineEval (L t.i) (intersection (L t.j) (L t.k))) with h | h
    · exact Or.inl ⟨le_rfl,le_rfl,h⟩
    · exact Or.inr ⟨le_rfl,le_rfl,h⟩
  by_cases hrj : r.val=t.j
  · rw [hrj,intersection_on_right _ _ hijp,intersection_on_left _ _ hjkp]
    rcases le_total 0 (affineEval (L t.j) (intersection (L t.i) (L t.k))) with h | h
    · exact Or.inl ⟨le_rfl,h,le_rfl⟩
    · exact Or.inr ⟨le_rfl,h,le_rfl⟩
  have hri' : r ≠ (⟨t.i,hin⟩ : Fin n) := by intro hh; exact hri (congrArg Fin.val hh)
  have hrj' : r ≠ (⟨t.j,hjn⟩ : Fin n) := by intro hh; exact hrj (congrArg Fin.val hh)
  have hnd := no_concurrent_at_pair n L hs ⟨t.i,hin⟩ ⟨t.j,hjn⟩ r hij hri' hrj'
  have hnda : affineEval (L r) (intersection (L t.i) (L t.j)) ≠ 0 := by
    rw [eval_intersection _ _ _ hijp]
    exact div_ne_zero hnd hijp
  have hir : det (L t.i) (L r) ≠ 0 := det_ne_of_ne n L hp ⟨t.i,hin⟩ r (Ne.symm hri')
  have hjr : det (L t.j) (L r) ≠ 0 := det_ne_of_ne n L hp ⟨t.j,hjn⟩ r (Ne.symm hrj')
  have hproducti := outside_evaluation_product (L r) (L t.i) (L t.j) (L t.k) w
    hijp hikp hir hwi (hi r hri)
  have houtj := hj r hrj
  rw [intersection_swap (L t.i) (L t.j)] at houtj
  have hproductj := outside_evaluation_product (L r) (L t.j) (L t.i) (L t.k) w
    hjip hjkp hjr hwj houtj
  rw [← intersection_swap (L t.i) (L t.j)] at hproductj
  exact three_signs _ _ _ hnda hproducti hproductj

#print axioms triangle_of_two_sides

/-- The same emptiness criterion using the sides supported by the last two
lines. This is the useful orientation for an old line and two added BBL lines. -/
theorem triangle_of_last_two_sides (n : Nat) (L : Nat → Line ℝ) (w : Line ℝ)
    (hp : NoParallel n L) (hs : NoConcurrent n L) (hw : Admissible n L w)
    (t : Triple) (hij : t.i < t.j) (hjk : t.j < t.k) (hkn : t.k < n)
    (hj : ∀ r : Fin n, r.val ≠ t.j → Outside
      (projection w (intersection (L t.j) (L r)))
      (projection w (intersection (L t.j) (L t.k)))
      (projection w (intersection (L t.i) (L t.j))))
    (hk : ∀ r : Fin n, r.val ≠ t.k → Outside
      (projection w (intersection (L t.k) (L r)))
      (projection w (intersection (L t.j) (L t.k)))
      (projection w (intersection (L t.i) (L t.k)))) : TrianglePredicate n L t := by
  have hin : t.i < n := by omega
  have hjn : t.j < n := by omega
  have hijp := hp ⟨t.i,hin⟩ ⟨t.j,hjn⟩ hij
  have hikp := hp ⟨t.i,hin⟩ ⟨t.k,hkn⟩ (show t.i < t.k from lt_trans hij hjk)
  have hjkp := hp ⟨t.j,hjn⟩ ⟨t.k,hkn⟩ hjk
  have hjip : det (L t.j) (L t.i) ≠ 0 := by
    rw [det_skew]; exact neg_ne_zero.mpr hijp
  have hkip : det (L t.k) (L t.i) ≠ 0 := by
    rw [det_skew]; exact neg_ne_zero.mpr hikp
  have hkjp : det (L t.k) (L t.j) ≠ 0 := by
    rw [det_skew]; exact neg_ne_zero.mpr hjkp
  have hwj : det w (L t.j) ≠ 0 := by
    rw [det_skew]; exact neg_ne_zero.mpr (hw ⟨t.j,hjn⟩)
  have hwk : det w (L t.k) ≠ 0 := by
    rw [det_skew]; exact neg_ne_zero.mpr (hw ⟨t.k,hkn⟩)
  refine ⟨hij,hjk,hkn,hs ⟨t.i,hin⟩ ⟨t.j,hjn⟩ ⟨t.k,hkn⟩ hij hjk,?_⟩
  intro r
  rw [oriented_nonneg_iff _ _ _ hijp,oriented_nonneg_iff _ _ _ hikp,
    oriented_nonneg_iff _ _ _ hjkp,oriented_nonpos_iff _ _ _ hijp,
    oriented_nonpos_iff _ _ _ hikp,oriented_nonpos_iff _ _ _ hjkp]
  by_cases hrj : r.val = t.j
  · rw [hrj,intersection_on_right _ _ hijp,intersection_on_left _ _ hjkp]
    rcases le_total 0 (affineEval (L t.j) (intersection (L t.i) (L t.k))) with h | h
    · exact Or.inl ⟨le_rfl,h,le_rfl⟩
    · exact Or.inr ⟨le_rfl,h,le_rfl⟩
  by_cases hrk : r.val = t.k
  · rw [hrk,intersection_on_right _ _ hikp,intersection_on_right _ _ hjkp]
    rcases le_total 0 (affineEval (L t.k) (intersection (L t.i) (L t.j))) with h | h
    · exact Or.inl ⟨h,le_rfl,le_rfl⟩
    · exact Or.inr ⟨h,le_rfl,le_rfl⟩
  have hrj' : r ≠ (⟨t.j,hjn⟩ : Fin n) := by intro hh; exact hrj (congrArg Fin.val hh)
  have hrk' : r ≠ (⟨t.k,hkn⟩ : Fin n) := by intro hh; exact hrk (congrArg Fin.val hh)
  have hnd := no_concurrent_at_pair n L hs ⟨t.j,hjn⟩ ⟨t.k,hkn⟩ r hjk hrj' hrk'
  have hnda : affineEval (L r) (intersection (L t.j) (L t.k)) ≠ 0 := by
    rw [eval_intersection _ _ _ hjkp]; exact div_ne_zero hnd hjkp
  have hjr := det_ne_of_ne n L hp ⟨t.j,hjn⟩ r (Ne.symm hrj')
  have hkr := det_ne_of_ne n L hp ⟨t.k,hkn⟩ r (Ne.symm hrk')
  have houtj := hj r hrj
  rw [intersection_swap (L t.i) (L t.j)] at houtj
  have hpj := outside_evaluation_product (L r) (L t.j) (L t.k) (L t.i) w
    hjkp hjip hjr hwj houtj
  rw [← intersection_swap (L t.i) (L t.j)] at hpj
  have houtk := hk r hrk
  rw [intersection_swap (L t.j) (L t.k),intersection_swap (L t.i) (L t.k)] at houtk
  have hpk := outside_evaluation_product (L r) (L t.k) (L t.j) (L t.i) w
    hkjp hkip hkr hwk houtk
  rw [← intersection_swap (L t.j) (L t.k),← intersection_swap (L t.i) (L t.k)] at hpk
  rcases three_signs _ _ _ hnda hpj hpk with h | h
  · exact Or.inl ⟨h.2.1,h.2.2,h.1⟩
  · exact Or.inr ⟨h.2.1,h.2.2,h.1⟩

#print axioms triangle_of_last_two_sides
end Kobon.BBLTriangles
