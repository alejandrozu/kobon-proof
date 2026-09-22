import Kobon.BBLTriangles

/-! Simplicity of an enlarged arrangement from the old arrangement and the
strict crossing order on each added line. No new triple determinant is
assumed nonzero. -/
namespace Kobon.BBLSimple
open Exterior BBLTriangles BBLExtrema

theorem point_eq_intersection (l m : Line ℝ) (p : Point) (hd : det l m≠0)
    (hl : affineEval l p=0) (hm : affineEval m p=0) : p=intersection l m := by
  have hx1 := congrArg (fun z => z*m.b) hl
  have hx2 := congrArg (fun z => z*l.b) hm
  have hy1 := congrArg (fun z => z*m.a) hl
  have hy2 := congrArg (fun z => z*l.a) hm
  apply Prod.ext
  · dsimp [intersection,vertex]
    apply (eq_div_iff hd).mpr
    dsimp [affineEval,det] at *
    nlinarith only [hx1,hx2]
  · dsimp [intersection,vertex]
    apply (eq_div_iff hd).mpr
    dsimp [affineEval,det] at *
    nlinarith only [hy1,hy2]

theorem equal_intersections_of_concurrent (l m s : Line ℝ)
    (hlm : det l m≠0) (hls : det l s≠0) (he : evalVertex s l m=0) :
    intersection l m=intersection l s := by
  apply point_eq_intersection l s _ hls (intersection_on_left l m hlm)
  rw [eval_intersection s l m hlm,he,zero_div]

def RowInjective (n : Nat) (L : Nat → Line ℝ) (w : Line ℝ) (r : Fin n) : Prop :=
  ∀ i j : Fin n, i≠r → j≠r →
    projection w (intersection (L r) (L i))=projection w (intersection (L r) (L j)) → i=j

theorem row_excludes_concurrence (n : Nat) (L : Nat → Line ℝ) (w : Line ℝ)
    (hp : NoParallel n L) (r i j : Fin n) (hr : RowInjective n L w r)
    (hri : i≠r) (hrj : j≠r) (hij : i≠j) :
    evalVertex (L r) (L i) (L j)≠0 := by
  intro hz
  have hdri := det_ne_of_ne n L hp r i (Ne.symm hri)
  have hdrj := det_ne_of_ne n L hp r j (Ne.symm hrj)
  have he : evalVertex (L j) (L r) (L i)=0 := by
    rw [← eval_cyclic]
    exact hz
  have heq := equal_intersections_of_concurrent (L r) (L i) (L j) hdri hdrj he
  exact hij (hr i j hri hrj (congrArg (projection w) heq))

/-- Only triples containing an added line need a crossing-row argument. -/
theorem no_concurrent_of_old_and_rows (n : Nat) (L : Nat → Line ℝ) (w : Line ℝ)
    (added : Fin n → Prop) (hp : NoParallel n L)
    (hold : ∀ i j k : Fin n, i<j → j<k →
      ¬added i → ¬added j → ¬added k → evalVertex (L k) (L i) (L j)≠0)
    (hrows : ∀ r, added r → RowInjective n L w r) : NoConcurrent n L := by
  intro i j k hij hjk
  have hik : i<k := lt_trans hij hjk
  by_cases hk : added k
  · exact row_excludes_concurrence n L w hp k i j (hrows k hk)
      (ne_of_lt hik) (ne_of_lt hjk) (ne_of_lt hij)
  by_cases hi : added i
  · rw [eval_cyclic,eval_cyclic]
    exact row_excludes_concurrence n L w hp i j k (hrows i hi)
      (ne_of_gt hij) (ne_of_gt hik) (ne_of_lt hjk)
  by_cases hj : added j
  · rw [eval_cyclic]
    exact row_excludes_concurrence n L w hp j k i (hrows j hj)
      (ne_of_gt hjk) (ne_of_lt hij) (ne_of_gt hik)
  exact hold i j k hij hjk hi hj hk

/-- Canonical BBL labels: q old nonhorizontal lines, q added lines, then Y0.
The old input labels Y0 first. Strict new rows force simplicity of the whole
enlarged real arrangement. -/
theorem canonical_no_concurrent (q : Nat) (L O : Nat → Line ℝ) (w : Line ℝ)
    (hp : NoParallel (2*q+1) L) (hs : NoConcurrent (q+1) O)
    (hold : ∀ j, j<q → L j=O (j+1)) (hzero : L (2*q)=O 0)
    (hrows : ∀ r : Fin (2*q+1), q≤r.val → r.val<2*q →
      RowInjective (2*q+1) L w r) : NoConcurrent (2*q+1) L := by
  apply no_concurrent_of_old_and_rows (2*q+1) L w (fun r => q≤r.val ∧ r.val<2*q) hp
  · intro i j k hij hjk hi hj hk
    have hiv : i.val<j.val := hij
    have hjv : j.val<k.val := hjk
    have hin : i.val<q := by omega
    have hjn : j.val<q := by omega
    by_cases hkn : k.val<q
    · rw [hold i hin,hold j hjn,hold k hkn]
      exact hs ⟨i.val+1,by omega⟩ ⟨j.val+1,by omega⟩ ⟨k.val+1,by omega⟩
        (show i.val+1<j.val+1 by omega) (show j.val+1<k.val+1 by omega)
    · have hkeq : k.val=2*q := by omega
      rw [hold i hin,hold j hjn,hkeq,hzero,eval_cyclic]
      exact hs ⟨0,by omega⟩ ⟨i.val+1,by omega⟩ ⟨j.val+1,by omega⟩
        (show 0 < i.val+1 by omega) (show i.val+1<j.val+1 by omega)
  · intro r hr
    exact hrows r hr.1 hr.2

#print axioms canonical_no_concurrent
end Kobon.BBLSimple
