import Kobon.BBLPersistence

/-! Actual replacement of an old distinguished triangle by a nearby cap line.
Only the two delicate endpoint signs against the near-horizontal pencil are
left as hypotheses; all old-line tests and the new apex tests follow from
strictness and continuity. The endpoint hypotheses are supplied separately
by the BBL crossing-order lemmas. -/
namespace Kobon.BBLCapReplacement
open BBLPersistence BBLTriangles BBLExtrema Exterior Filter
open scoped Topology

theorem oriented_swap (r l m : Line ℝ) : orientedEval r l m=orientedEval r m l := by
  dsimp [orientedEval,evalVertex,vertex,det]
  ring

@[simp] theorem oriented_self_left (l m : Line ℝ) : orientedEval l l m=0 := by
  dsimp [orientedEval,evalVertex,vertex,det]
  ring

@[simp] theorem oriented_self_right (l m : Line ℝ) : orientedEval m l m=0 := by
  dsimp [orientedEval,evalVertex,vertex,det]
  ring

theorem weakSigns_aligned (v x y z : ℝ) (hv : v≠0)
    (hx : 0≤v*x) (hy : 0≤v*y) (hz : 0≤v*z) : weakSigns x y z := by
  rcases lt_or_gt_of_ne hv with hv | hv
  · right
    have step (a : ℝ) (ha : 0≤v*a) : a≤0 := by
      by_contra hh
      have hm := mul_neg_of_neg_of_pos hv (lt_of_not_ge hh)
      linarith
    exact ⟨step x hx,step y hy,step z hz⟩
  · left
    exact ⟨(mul_nonneg_iff_of_pos_left hv).mp hx,
      (mul_nonneg_iff_of_pos_left hv).mp hy,(mul_nonneg_iff_of_pos_left hv).mp hz⟩

theorem support_left (l m s : Line ℝ) : weakSigns
    (orientedEval l l m) (orientedEval l l s) (orientedEval l m s) := by
  simp only [oriented_self_left]
  rcases le_total 0 (orientedEval l m s) with h | h
  · exact Or.inl ⟨le_rfl,le_rfl,h⟩
  · exact Or.inr ⟨le_rfl,le_rfl,h⟩

theorem support_right (l m s : Line ℝ) : weakSigns
    (orientedEval m l m) (orientedEval m l s) (orientedEval m m s) := by
  simp only [oriented_self_left,oriented_self_right]
  rcases le_total 0 (orientedEval m l s) with h | h
  · exact Or.inl ⟨le_rfl,h,le_rfl⟩
  · exact Or.inr ⟨le_rfl,h,le_rfl⟩

/-- Every test against a line not supporting a simple triangular cell is strict. -/
theorem triangle_strict_test (n : Nat) (L : Nat → Line ℝ)
    (hp : NoParallel n L) (hs : NoConcurrent n L) (t : Triple)
    (ht : TrianglePredicate n L t) (r : Fin n)
    (hri : r.val≠t.i) (hrj : r.val≠t.j) (hrk : r.val≠t.k) :
    strictSigns (orientedEval (L r) (L t.i) (L t.j))
      (orientedEval (L r) (L t.i) (L t.k))
      (orientedEval (L r) (L t.j) (L t.k)) := by
  obtain ⟨hij,hjk,hkn,_,htri⟩ := ht
  have hin : t.i<n := by omega
  have hjn : t.j<n := by omega
  have hri' : r≠(⟨t.i,hin⟩ : Fin n) := by intro h; exact hri (congrArg Fin.val h)
  have hrj' : r≠(⟨t.j,hjn⟩ : Fin n) := by intro h; exact hrj (congrArg Fin.val h)
  have hrk' : r≠(⟨t.k,hkn⟩ : Fin n) := by intro h; exact hrk (congrArg Fin.val h)
  apply strict_of_weak _ _ _ (htri r)
  · exact mul_ne_zero (no_concurrent_at_pair n L hs ⟨t.i,hin⟩ ⟨t.j,hjn⟩ r hij hri' hrj')
      (hp ⟨t.i,hin⟩ ⟨t.j,hjn⟩ hij)
  · exact mul_ne_zero (no_concurrent_at_pair n L hs ⟨t.i,hin⟩ ⟨t.k,hkn⟩ r
      (show t.i < t.k from lt_trans hij hjk) hri' hrk')
      (hp ⟨t.i,hin⟩ ⟨t.k,hkn⟩ (show t.i < t.k from lt_trans hij hjk))
  · exact mul_ne_zero (no_concurrent_at_pair n L hs ⟨t.j,hjn⟩ ⟨t.k,hkn⟩ r hjk hrj' hrk')
      (hp ⟨t.j,hjn⟩ ⟨t.k,hkn⟩ hjk)

theorem old_test_eventually (R Y A B D : Line ℝ)
    (ht : strictSigns (orientedEval R Y A) (orientedEval R Y B) (orientedEval R A B)) :
    ∀ᶠ κ in 𝓝 (0:ℝ), weakSigns (orientedEval R A B)
      (orientedEval R A (perturb Y D κ)) (orientedEval R B (perturb Y D κ)) := by
  have h0 : strictSigns (orientedEval R A B)
      (orientedEval R A (perturb Y D 0)) (orientedEval R B (perturb Y D 0)) := by
    simp only [perturb_zero,oriented_swap R A Y,oriented_swap R B Y]
    rcases ht with h | h
    · exact Or.inl ⟨h.2.2,h.1,h.2.1⟩
    · exact Or.inr ⟨h.2.2,h.1,h.2.1⟩
  have hA : ContinuousAt (fun κ => orientedEval R A (perturb Y D κ)) 0 := by
    dsimp [orientedEval,evalVertex,vertex,det,perturb]
    fun_prop
  have hB : ContinuousAt (fun κ => orientedEval R B (perturb Y D κ)) 0 := by
    dsimp [orientedEval,evalVertex,vertex,det,perturb]
    fun_prop
  exact (strictSigns_eventually _ _ _ 0 continuousAt_const hA hB h0).mono
    (fun _ hh => weak_of_strict _ _ _ hh)

theorem apex_test_eventually (Y A B D : Line ℝ) (hv : orientedEval Y A B≠0) :
    ∀ᶠ κ in 𝓝 (0:ℝ), 0<orientedEval Y A B*orientedEval (perturb Y D κ) A B := by
  have hc : ContinuousAt (fun κ => orientedEval Y A B*orientedEval (perturb Y D κ) A B) 0 := by
    dsimp [orientedEval,evalVertex,vertex,det,perturb]
    fun_prop
  have hp : 0<orientedEval Y A B*orientedEval (perturb Y D 0) A B := by
    simpa [pow_two] using sq_pos_of_ne_zero hv
  exact Filter.Tendsto.eventually_const_lt hp hc

/-- The endpoint signs that are not supplied by ordinary strict continuity.
They concern the old distinguished line and the added pencil only. -/
def EndpointSigns (n m c i j : Nat) (L D : Nat → Line ℝ) (κ : ℝ) : Prop :=
  let M := perturb (L 0) (D c) κ
  let v := orientedEval (L 0) (L i) (L j)
  ∀ r : Fin (n+m), r.val=0 ∨ n≤r.val →
    0≤v*orientedEval (pencilAppend n L D 0 κ r) (L i) M ∧
    0≤v*orientedEval (pencilAppend n L D 0 κ r) (L j) M

/-- For a finite pencil converging to Y0, every old distinguished triangle
has a valid nearby cap as soon as the explicit endpoint signs hold. -/
theorem cap_replacement_eventually (n m c i j : Nat) (L D : Nat → Line ℝ)
    (hp : NoParallel n L) (hs : NoConcurrent n L)
    (ht : TrianglePredicate n L ⟨0,i,j⟩) (hc : c<m) :
    ∀ᶠ κ in 𝓝 (0:ℝ), EndpointSigns n m c i j L D κ →
      TrianglePredicate (n+m) (pencilAppend n L D 0 κ) ⟨i,j,n+c⟩ := by
  have hi : 0 < i := ht.1
  have hij : i < j := ht.2.1
  have hjn : j < n := ht.2.2.1
  have hin : i < n := lt_trans hij hjn
  have hzn : 0 < n := by omega
  let v := orientedEval (L 0) (L i) (L j)
  have hev : evalVertex (L 0) (L i) (L j)≠0 := by
    rw [eval_cyclic]
    exact ht.2.2.2.1
  have hv : v≠0 := mul_ne_zero hev (hp ⟨i,hin⟩ ⟨j,hjn⟩ hij)
  have hold : ∀ᶠ κ in 𝓝 (0:ℝ), ∀ r : Fin n,
      r.val≠0 → r.val≠i → r.val≠j →
      weakSigns (orientedEval (L r) (L i) (L j))
        (orientedEval (L r) (L i) (perturb (L 0) (D c) κ))
        (orientedEval (L r) (L j) (perturb (L 0) (D c) κ)) := by
    apply Filter.eventually_all.mpr
    intro r
    by_cases h0 : r.val=0
    · exact Filter.Eventually.of_forall (by intro κ h; exact (h h0).elim)
    by_cases hri : r.val=i
    · exact Filter.Eventually.of_forall (by intro κ _ h; exact (h hri).elim)
    by_cases hrj : r.val=j
    · exact Filter.Eventually.of_forall (by intro κ _ _ h; exact (h hrj).elim)
    exact (old_test_eventually (L r) (L 0) (L i) (L j) (D c)
      (triangle_strict_test n L hp hs _ ht r h0 hri hrj)).mono (fun _ h _ _ _ => h)
  have hnew : ∀ᶠ κ in 𝓝 (0:ℝ), ∀ s : Fin m,
      0<v*orientedEval (perturb (L 0) (D s) κ) (L i) (L j) := by
    apply Filter.eventually_all.mpr
    intro s
    exact apex_test_eventually _ _ _ _ hv
  apply (hold.and hnew).mono
  intro κ hκ he
  have hncap : ¬n+c<n := by omega
  have hM : pencilAppend n L D 0 κ (n+c)=perturb (L 0) (D c) κ := by
    simp [pencilAppend,hncap]
  dsimp only [TrianglePredicate]
  refine ⟨hij,by omega,by omega,?_,?_⟩
  · simp only [pencilAppend,if_pos hin,if_pos hjn,if_neg hncap,Nat.add_sub_cancel_left]
    have hh := hκ.2 ⟨c,hc⟩
    intro hz
    simp [orientedEval,hz] at hh
  intro r
  simp only [pencilAppend,if_pos hin,if_pos hjn,if_neg hncap,Nat.add_sub_cancel_left]
  by_cases hrn : r.val<n
  · rw [if_pos hrn]
    by_cases hri : r.val=i
    · subst i
      exact support_left _ _ _
    by_cases hrj : r.val=j
    · subst j
      exact support_right _ _ _
    by_cases hr0 : r.val=0
    · have he' := he r (Or.inl hr0)
      simp only [pencilAppend,if_pos hrn] at he'
      apply weakSigns_aligned v _ _ _ hv
      · simpa [hr0,v,pow_two] using sq_nonneg v
      · exact he'.1
      · exact he'.2
    · exact hκ.1 ⟨r.val,hrn⟩ hr0 hri hrj
  · rw [if_neg hrn]
    have hrs : r.val-n<m := by omega
    have he' := he r (Or.inr (by omega))
    simp only [pencilAppend,if_neg hrn] at he'
    exact weakSigns_aligned v _ _ _ hv (le_of_lt (hκ.2 ⟨r.val-n,hrs⟩)) he'.1 he'.2

#print axioms cap_replacement_eventually
end Kobon.BBLCapReplacement
