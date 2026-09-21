import Kobon.Euclidean
import Kobon.Simple
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! Real geometric exterior addition, valid for either parity.

Visible pairs are specified by signs of affine values and directional
derivatives on the old arrangement. They are not defined by the desired
conclusion about triangles in the enlarged arrangement.
The missing global bound on the number of such pairs is a separate obligation.
-/
namespace Kobon.Exterior

noncomputable def projection (w : Line ℝ) (p : Point) : ℝ := w.a*p.1+w.b*p.2
def levelLine (w : Line ℝ) (H : ℝ) : Line ℝ := ⟨w.a,w.b,H⟩
def append (n : Nat) (L : Nat → Line ℝ) (l : Line ℝ) (i : Nat) : Line ℝ :=
  if i<n then L i else l

@[simp] theorem append_old (n : Nat) (L : Nat → Line ℝ) (l : Line ℝ)
    (i : Nat) (hi : i<n) : append n L l i=L i := if_pos hi
@[simp] theorem append_new (n : Nat) (L : Nat → Line ℝ) (l : Line ℝ) :
    append n L l n=l := by simp [append]

def Admissible (n : Nat) (L : Nat → Line ℝ) (w : Line ℝ) : Prop :=
  ∀ i : Fin n, det (L i) w ≠ 0
def Beyond (n : Nat) (L : Nat → Line ℝ) (w : Line ℝ) (H : ℝ) : Prop :=
  ∀ i j : Fin n, i<j → projection w (intersection (L i) (L j)) < H

@[simp] theorem det_level_right (l w : Line ℝ) (H : ℝ) :
    det l (levelLine w H)=det l w := rfl

theorem level_eval (w : Line ℝ) (H : ℝ) (p : Point) :
    affineEval (levelLine w H) p=projection w p-H := rfl

theorem level_nondegenerate (l m w : Line ℝ) (H : ℝ) (hp : det l m ≠ 0)
    (hH : projection w (intersection l m)<H) : evalVertex (levelLine w H) l m ≠ 0 := by
  intro hz
  have h := eval_intersection (levelLine w H) l m hp
  rw [hz,zero_div,level_eval] at h
  linarith

theorem no_parallel (n : Nat) (L : Nat → Line ℝ) (w : Line ℝ) (H : ℝ)
    (hp : NoParallel n L) (hw : Admissible n L w) :
    NoParallel (n+1) (append n L (levelLine w H)) := by
  intro i j hij
  have hi : i.val<n := by omega
  by_cases hj : j.val<n
  · simpa [hi,hj] using hp ⟨i.val,hi⟩ ⟨j.val,hj⟩ hij
  · have hjn : j.val=n := by omega
    simpa [hi,hjn] using hw ⟨i.val,hi⟩

theorem no_concurrent (n : Nat) (L : Nat → Line ℝ) (w : Line ℝ) (H : ℝ)
    (hp : NoParallel n L) (hs : NoConcurrent n L) (hH : Beyond n L w H) :
    NoConcurrent (n+1) (append n L (levelLine w H)) := by
  intro i j k hij hjk
  have hi : i.val<n := by omega
  have hj : j.val<n := by omega
  by_cases hk : k.val<n
  · simpa [hi,hj,hk] using hs ⟨i.val,hi⟩ ⟨j.val,hj⟩ ⟨k.val,hk⟩ hij hjk
  · have hkn : k.val=n := by omega
    simpa [hi,hj,hkn] using level_nondegenerate (L i) (L j) w H
      (hp ⟨i.val,hi⟩ ⟨j.val,hj⟩ hij) (hH ⟨i.val,hi⟩ ⟨j.val,hj⟩ hij)

theorem preserves_triangle (n : Nat) (L : Nat → Line ℝ) (w : Line ℝ) (H : ℝ)
    (hp : NoParallel n L) (hH : Beyond n L w H) (t : Triple)
    (ht : TrianglePredicate n L t) :
    TrianglePredicate (n+1) (append n L (levelLine w H)) t := by
  rcases ht with ⟨hij,hjk,hkn,hnd,ht⟩
  have hin : t.i<n := by omega
  have hjn : t.j<n := by omega
  refine ⟨hij,hjk,by omega,by simpa [hin,hjn,hkn] using hnd,?_⟩
  intro r
  by_cases hr : r.val<n
  · simpa [hr,hin,hjn,hkn] using ht ⟨r.val,hr⟩
  · have hrn : r.val=n := by omega
    simp only [hrn,append_new,append_old n L _ t.i hin,append_old n L _ t.j hjn,
      append_old n L _ t.k hkn]
    right
    have pair (i j : Fin n) (hij : i<j) :
        orientedEval (levelLine w H) (L i) (L j) ≤ 0 := by
      apply (oriented_nonpos_iff _ _ _ (hp i j hij)).mpr
      rw [level_eval]
      linarith [hH i j hij]
    exact ⟨pair ⟨t.i,hin⟩ ⟨t.j,hjn⟩ hij,
      pair ⟨t.i,hin⟩ ⟨t.k,hkn⟩ (show t.i<t.k from lt_trans hij hjk),
      pair ⟨t.j,hjn⟩ ⟨t.k,hkn⟩ hjk⟩

/-- Derivative of r along l, parameterized so that projection w increases at unit speed. -/
noncomputable def derivative (r l w : Line ℝ) : ℝ := det r l / det w l

theorem ray_evaluation (r l m w : Line ℝ) (H : ℝ)
    (hlm : det l m ≠ 0) (hlw : det l w ≠ 0) :
    affineEval r (intersection l (levelLine w H)) =
      affineEval r (intersection l m) +
      (H-projection w (intersection l m))*derivative r l w := by
  have heq : det w l = -det l w := by dsimp [det]; ring
  unfold derivative
  rw [heq,div_neg]
  dsimp [affineEval,intersection,vertex,levelLine,projection,det] at hlm hlw ⊢
  have hnorm : w.b*l.a-l.b*w.a ≠ 0 := by simpa only [mul_comm w.b l.a] using hlw
  field_simp [hnorm]
  ring

def VisiblePair (n : Nat) (L : Nat → Line ℝ) (w : Line ℝ) (t : Triple) : Prop :=
  t.i<t.j ∧ t.j<n ∧ t.k=n ∧ ∀ r : Fin n,
    (0 ≤ affineEval (L r) (intersection (L t.i) (L t.j)) ∧
     0 ≤ derivative (L r) (L t.i) w ∧ 0 ≤ derivative (L r) (L t.j) w) ∨
    (affineEval (L r) (intersection (L t.i) (L t.j)) ≤ 0 ∧
     derivative (L r) (L t.i) w ≤ 0 ∧ derivative (L r) (L t.j) w ≤ 0)

theorem intersection_swap (l m : Line ℝ) : intersection l m=intersection m l := by
  dsimp [intersection,vertex]
  have hd : det m l = -det l m := by dsimp [det]; ring
  rw [hd]
  have hx : m.c*l.b-m.b*l.c = -(l.c*m.b-l.b*m.c) := by ring
  have hy : m.a*l.c-m.c*l.a = -(l.a*m.c-l.c*m.a) := by ring
  rw [hx,hy]
  simp only [neg_div_neg_eq]

theorem visible_triangle (n : Nat) (L : Nat → Line ℝ) (w : Line ℝ) (H : ℝ)
    (hp : NoParallel n L) (hw : Admissible n L w) (hH : Beyond n L w H)
    (t : Triple) (ht : VisiblePair n L w t) :
    TrianglePredicate (n+1) (append n L (levelLine w H)) t := by
  rcases ht with ⟨hij,hjn,hkn,ht⟩
  have hin : t.i<n := by omega
  have hdet : det (L t.i) (L t.j) ≠ 0 := hp ⟨t.i,hin⟩ ⟨t.j,hjn⟩ hij
  have hdi : det (L t.i) w ≠ 0 := hw ⟨t.i,hin⟩
  have hdj : det (L t.j) w ≠ 0 := hw ⟨t.j,hjn⟩
  have hdiH : det (L t.i) (levelLine w H) ≠ 0 := hdi
  have hdjH : det (L t.j) (levelLine w H) ≠ 0 := hdj
  have hgt : projection w (intersection (L t.i) (L t.j))<H := hH ⟨t.i,hin⟩ ⟨t.j,hjn⟩ hij
  have hdets : det (L t.j) (L t.i) ≠ 0 := by
    have heq : det (L t.j) (L t.i) = -det (L t.i) (L t.j) := by dsimp [det]; ring
    rw [heq]
    exact neg_ne_zero.mpr hdet
  refine ⟨hij,by omega,by omega,?_,?_⟩
  · simpa [hin,hjn,hkn] using level_nondegenerate (L t.i) (L t.j) w H hdet hgt
  · intro r
    by_cases hr : r.val<n
    · simp only [append_old n L _ r.val hr,append_old n L _ t.i hin,
        append_old n L _ t.j hjn,hkn,append_new]
      rw [oriented_nonneg_iff _ _ _ hdet,oriented_nonneg_iff _ _ _ hdiH,
        oriented_nonneg_iff _ _ _ hdjH,oriented_nonpos_iff _ _ _ hdet,
        oriented_nonpos_iff _ _ _ hdiH,oriented_nonpos_iff _ _ _ hdjH]
      rw [ray_evaluation (L r) (L t.i) (L t.j) w H hdet hdi,
        ray_evaluation (L r) (L t.j) (L t.i) w H hdets hdj,
        ← intersection_swap (L t.i) (L t.j)]
      have hd : 0 ≤ H-projection w (intersection (L t.i) (L t.j)) := by linarith
      rcases ht ⟨r.val,hr⟩ with ⟨ha,hb,hc⟩ | ⟨ha,hb,hc⟩
      · exact Or.inl ⟨ha,add_nonneg ha (mul_nonneg hd hb),add_nonneg ha (mul_nonneg hd hc)⟩
      · exact Or.inr ⟨ha,add_nonpos ha (mul_nonpos_of_nonneg_of_nonpos hd hb),
          add_nonpos ha (mul_nonpos_of_nonneg_of_nonpos hd hc)⟩
    · have hrn : r.val=n := by omega
      simp only [hrn,append_new,append_old n L _ t.i hin,
        append_old n L _ t.j hjn,hkn]
      right
      rw [oriented_nonpos_iff _ _ _ hdet,oriented_nonpos_iff _ _ _ hdiH,
        oriented_nonpos_iff _ _ _ hdjH,intersection_on_right _ _ hdiH,
        intersection_on_right _ _ hdjH,level_eval]
      exact ⟨by linarith,le_rfl,le_rfl⟩

/-- Count-preserving exterior extension plus every explicitly visible old pair.
No parity restriction and no assumption about a future triangle count. -/
theorem extension (n T : Nat) (L : Nat → Line ℝ) (ts ns : List Triple)
    (w : Line ℝ) (H : ℝ) (hp : NoParallel n L) (hs : NoConcurrent n L)
    (hnt : ts.Nodup) (ht : ∀ t ∈ ts, TrianglePredicate n L t) (hc : T ≤ ts.length)
    (hnn : ns.Nodup) (hn : ∀ t ∈ ns, VisiblePair n L w t)
    (hw : Admissible n L w) (hH : Beyond n L w H) :
    SimpleLowerBound (n+1) (T+ns.length) := by
  have hd : List.Disjoint ts ns := by
    apply List.disjoint_left.mpr
    intro t hts hns
    have hold := (ht t hts).2.2.1
    have hnew := (hn t hns).2.2.1
    omega
  refine ⟨append n L (levelLine w H),no_parallel n L w H hp hw,
    no_concurrent n L w H hp hs hH,ts++ns,List.nodup_append.mpr ⟨hnt,hnn,?_⟩,?_,?_⟩
  · intro a ha b hb hab
    subst b
    exact (List.disjoint_left.mp hd) ha hb
  · intro t hm
    rcases List.mem_append.mp hm with hm | hm
    · exact preserves_triangle n L w H hp hH t (ht t hm)
    · exact visible_triangle n L w H hp hw hH t (hn t hm)
  · simpa only [List.length_append] using Nat.add_le_add_right hc ns.length

/-- An explicit height strictly beyond every old vertex. -/
noncomputable def safeHeight (n : Nat) (L : Nat → Line ℝ) (w : Line ℝ) : ℝ :=
  1+∑ i : Fin n, ∑ j : Fin n, |projection w (intersection (L i) (L j))|

theorem safeHeight_beyond (n : Nat) (L : Nat → Line ℝ) (w : Line ℝ) :
    Beyond n L w (safeHeight n L w) := by
  intro i j _
  have hrow : |projection w (intersection (L i) (L j))| ≤
      ∑ k : Fin n, |projection w (intersection (L i) (L k))| :=
    Finset.single_le_sum (f := fun k : Fin n => |projection w (intersection (L i) (L k))|)
      (fun k _ => abs_nonneg _) (Finset.mem_univ j)
  have htotal : (∑ k : Fin n, |projection w (intersection (L i) (L k))|) ≤
      ∑ l : Fin n, ∑ k : Fin n, |projection w (intersection (L l) (L k))| :=
    Finset.single_le_sum
      (f := fun l : Fin n => ∑ k : Fin n, |projection w (intersection (L l) (L k))|)
      (fun l _ => Finset.sum_nonneg (fun k _ => abs_nonneg _)) (Finset.mem_univ i)
  have h := le_abs_self (projection w (intersection (L i) (L j)))
  dsimp [safeHeight]
  linarith

#print axioms extension
#print axioms safeHeight_beyond
end Kobon.Exterior
