import Kobon.BBLTriangles
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Tactic.FunProp

/-! Openness of strict visibility tests.

Adding lines sufficiently close to an existing line preserves each visible
wedge whose two supports do not contain that existing line. This replaces
case-specific arguments about the exceptional two central rays.
-/
namespace Kobon.BBLPersistence
open Exterior HybridBoundary BBLExtrema BBLTriangles Filter
open scoped Topology

def weakSigns (x y z : ℝ) : Prop :=
  (0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z) ∨ (x ≤ 0 ∧ y ≤ 0 ∧ z ≤ 0)

def strictSigns (x y z : ℝ) : Prop :=
  (0 < x ∧ 0 < y ∧ 0 < z) ∨ (x < 0 ∧ y < 0 ∧ z < 0)

theorem strict_of_weak (x y z : ℝ) (h : weakSigns x y z)
    (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0) : strictSigns x y z := by
  rcases h with h | h
  · exact Or.inl ⟨lt_of_le_of_ne h.1 (Ne.symm hx),
      lt_of_le_of_ne h.2.1 (Ne.symm hy),lt_of_le_of_ne h.2.2 (Ne.symm hz)⟩
  · exact Or.inr ⟨lt_of_le_of_ne h.1 hx,lt_of_le_of_ne h.2.1 hy,
      lt_of_le_of_ne h.2.2 hz⟩

theorem weak_of_strict (x y z : ℝ) (h : strictSigns x y z) : weakSigns x y z := by
  rcases h with h | h
  · exact Or.inl ⟨le_of_lt h.1,le_of_lt h.2.1,le_of_lt h.2.2⟩
  · exact Or.inr ⟨le_of_lt h.1,le_of_lt h.2.1,le_of_lt h.2.2⟩

theorem strictSigns_eventually (f g h : ℝ → ℝ) (x : ℝ)
    (hf : ContinuousAt f x) (hg : ContinuousAt g x) (hh : ContinuousAt h x)
    (hs : strictSigns (f x) (g x) (h x)) :
    ∀ᶠ y in 𝓝 x, strictSigns (f y) (g y) (h y) := by
  rcases hs with hs | hs
  · have h1 := Filter.Tendsto.eventually_const_lt hs.1 hf
    have h2 := Filter.Tendsto.eventually_const_lt hs.2.1 hg
    have h3 := Filter.Tendsto.eventually_const_lt hs.2.2 hh
    exact (h1.and (h2.and h3)).mono (fun _ hy => Or.inl hy)
  · have h1 := Filter.Tendsto.eventually_lt_const hs.1 hf
    have h2 := Filter.Tendsto.eventually_lt_const hs.2.1 hg
    have h3 := Filter.Tendsto.eventually_lt_const hs.2.2 hh
    exact (h1.and (h2.and h3)).mono (fun _ hy => Or.inr hy)

def perturb (r d : Line ℝ) (κ : ℝ) : Line ℝ :=
  ⟨r.a+κ*d.a,r.b+κ*d.b,r.c+κ*d.c⟩

@[simp] theorem perturb_zero (r d : Line ℝ) : perturb r d 0 = r := by
  cases r
  simp [perturb]

theorem perturb_test_eventually (r d l m w : Line ℝ)
    (hv : weakSigns (affineEval r (intersection l m))
      (derivative r l w) (derivative r m w))
    (heval : affineEval r (intersection l m) ≠ 0)
    (hderivl : derivative r l w ≠ 0) (hderivm : derivative r m w ≠ 0) :
    ∀ᶠ κ in 𝓝 (0:ℝ), weakSigns (affineEval (perturb r d κ) (intersection l m))
      (derivative (perturb r d κ) l w) (derivative (perturb r d κ) m w) := by
  have hf : ContinuousAt (fun κ => affineEval (perturb r d κ) (intersection l m)) 0 := by
    dsimp [affineEval,perturb]
    fun_prop
  have hg : ContinuousAt (fun κ => derivative (perturb r d κ) l w) 0 := by
    dsimp [derivative,det,perturb]
    fun_prop
  have hh : ContinuousAt (fun κ => derivative (perturb r d κ) m w) 0 := by
    dsimp [derivative,det,perturb]
    fun_prop
  have hs := strict_of_weak _ _ _ hv heval hderivl hderivm
  have hs' : strictSigns (affineEval (perturb r d 0) (intersection l m))
      (derivative (perturb r d 0) l w) (derivative (perturb r d 0) m w) := by
    simpa using hs
  exact (strictSigns_eventually _ _ _ 0 hf hg hh hs').mono
    (fun _ hh => weak_of_strict _ _ _ hh)

/-- Every visibility test against an old line not supporting the wedge is
strict in a simple arrangement. Hence that line can be replaced by any small
coefficient perturbation without losing the test. -/
theorem visible_test_eventually (n : Nat) (L : Nat → Line ℝ) (w d : Line ℝ)
    (hp : NoParallel n L) (hs : NoConcurrent n L) (hw : Admissible n L w)
    (t : Triple) (ht : VisiblePair n L w t) (r : Fin n)
    (hri : r.val ≠ t.i) (hrj : r.val ≠ t.j) :
    ∀ᶠ κ in 𝓝 (0:ℝ), weakSigns
      (affineEval (perturb (L r) d κ) (intersection (L t.i) (L t.j)))
      (derivative (perturb (L r) d κ) (L t.i) w)
      (derivative (perturb (L r) d κ) (L t.j) w) := by
  have hij := ht.1
  have hjn := ht.2.1
  have hin : t.i < n := lt_trans hij hjn
  have hri' : r ≠ (⟨t.i,hin⟩ : Fin n) := by intro h; exact hri (congrArg Fin.val h)
  have hrj' : r ≠ (⟨t.j,hjn⟩ : Fin n) := by intro h; exact hrj (congrArg Fin.val h)
  have hijp := hp ⟨t.i,hin⟩ ⟨t.j,hjn⟩ hij
  apply perturb_test_eventually (L r) d (L t.i) (L t.j) w (ht.2.2.2 r)
  · rw [eval_intersection _ _ _ hijp]
    exact div_ne_zero (no_concurrent_at_pair n L hs ⟨t.i,hin⟩ ⟨t.j,hjn⟩ r hij hri' hrj') hijp
  · unfold derivative
    exact div_ne_zero (det_ne_of_ne n L hp r ⟨t.i,hin⟩ hri')
      (by rw [det_skew]; exact neg_ne_zero.mpr (hw ⟨t.i,hin⟩))
  · unfold derivative
    exact div_ne_zero (det_ne_of_ne n L hp r ⟨t.j,hjn⟩ hrj')
      (by rw [det_skew]; exact neg_ne_zero.mpr (hw ⟨t.j,hjn⟩))

#print axioms visible_test_eventually

def pencilAppend (n : Nat) (L D : Nat → Line ℝ) (r : Nat) (κ : ℝ)
    (i : Nat) : Line ℝ :=
  if i < n then L i else perturb (L r) (D (i-n)) κ

/-- Add an arbitrary finite pencil converging coefficientwise to one old line.
Every visible wedge not supported by that old line persists for small scale. -/
theorem visible_preserved_eventually (n m : Nat) (L D : Nat → Line ℝ) (w : Line ℝ)
    (hp : NoParallel n L) (hs : NoConcurrent n L) (hw : Admissible n L w)
    (t : Triple) (ht : VisiblePair n L w t) (r : Fin n)
    (hri : r.val ≠ t.i) (hrj : r.val ≠ t.j) :
    ∀ᶠ κ in 𝓝 (0:ℝ), VisiblePair (n+m) (pencilAppend n L D r κ) w
      ⟨t.i,t.j,n+m⟩ := by
  have hjn := ht.2.1
  have hin : t.i < n := lt_trans ht.1 hjn
  have hall : ∀ᶠ κ in 𝓝 (0:ℝ), ∀ s : Fin m, weakSigns
      (affineEval (perturb (L r) (D s) κ) (intersection (L t.i) (L t.j)))
      (derivative (perturb (L r) (D s) κ) (L t.i) w)
      (derivative (perturb (L r) (D s) κ) (L t.j) w) := by
    apply Filter.eventually_all.mpr
    intro s
    exact visible_test_eventually n L w (D s) hp hs hw t ht r hri hrj
  apply hall.mono
  intro κ hκ
  refine ⟨ht.1,(show t.j < n+m by omega),rfl,?_⟩
  intro s
  by_cases hsn : s.val < n
  · simpa [pencilAppend,hin,hjn,hsn] using ht.2.2.2 ⟨s.val,hsn⟩
  · have hsm : s.val-n < m := by omega
    simpa [pencilAppend,hin,hjn,hsn,weakSigns] using hκ ⟨s.val-n,hsm⟩

/-- Three nonzero same-sign vertex evaluations remain same-sign when a line
is perturbed. This is the old-triangle part of the BBL construction. -/
theorem triangle_test_eventually (r d : Line ℝ) (p q s : Point)
    (hv : weakSigns (affineEval r p) (affineEval r q) (affineEval r s))
    (hp : affineEval r p ≠ 0) (hq : affineEval r q ≠ 0)
    (hs : affineEval r s ≠ 0) :
    ∀ᶠ κ in 𝓝 (0:ℝ), weakSigns (affineEval (perturb r d κ) p)
      (affineEval (perturb r d κ) q) (affineEval (perturb r d κ) s) := by
  have hf : ContinuousAt (fun κ => affineEval (perturb r d κ) p) 0 := by
    dsimp [affineEval,perturb]; fun_prop
  have hg : ContinuousAt (fun κ => affineEval (perturb r d κ) q) 0 := by
    dsimp [affineEval,perturb]; fun_prop
  have hh : ContinuousAt (fun κ => affineEval (perturb r d κ) s) 0 := by
    dsimp [affineEval,perturb]; fun_prop
  have hst := strict_of_weak _ _ _ hv hp hq hs
  have hst' : strictSigns (affineEval (perturb r d 0) p)
      (affineEval (perturb r d 0) q) (affineEval (perturb r d 0) s) := by
    simpa using hst
  exact (strictSigns_eventually _ _ _ 0 hf hg hh hst').mono
    (fun _ hh => weak_of_strict _ _ _ hh)

#print axioms visible_preserved_eventually
#print axioms triangle_test_eventually

/-- Every old triangle not supported by the distinguished line survives any
finite pencil converging to that line. This is an actual triangle predicate
in the enlarged real straight-line arrangement. -/
theorem triangle_preserved_eventually (n m : Nat) (L D : Nat → Line ℝ)
    (hp : NoParallel n L) (hs : NoConcurrent n L)
    (t : Triple) (ht : TrianglePredicate n L t) (r : Fin n)
    (hri : r.val ≠ t.i) (hrj : r.val ≠ t.j) (hrk : r.val ≠ t.k) :
    ∀ᶠ κ in 𝓝 (0:ℝ), TrianglePredicate (n+m) (pencilAppend n L D r κ) t := by
  obtain ⟨hij,hjk,hkn,hnd,htri⟩ := ht
  have hin : t.i < n := by omega
  have hjn : t.j < n := by omega
  have hri' : r ≠ (⟨t.i,hin⟩ : Fin n) := by intro h; exact hri (congrArg Fin.val h)
  have hrj' : r ≠ (⟨t.j,hjn⟩ : Fin n) := by intro h; exact hrj (congrArg Fin.val h)
  have hrk' : r ≠ (⟨t.k,hkn⟩ : Fin n) := by intro h; exact hrk (congrArg Fin.val h)
  have hijp := hp ⟨t.i,hin⟩ ⟨t.j,hjn⟩ hij
  have hikp := hp ⟨t.i,hin⟩ ⟨t.k,hkn⟩ (show t.i < t.k from lt_trans hij hjk)
  have hjkp := hp ⟨t.j,hjn⟩ ⟨t.k,hkn⟩ hjk
  have hevij : affineEval (L r) (intersection (L t.i) (L t.j)) ≠ 0 := by
    rw [eval_intersection _ _ _ hijp]
    exact div_ne_zero (no_concurrent_at_pair n L hs ⟨t.i,hin⟩ ⟨t.j,hjn⟩ r hij hri' hrj') hijp
  have hevik : affineEval (L r) (intersection (L t.i) (L t.k)) ≠ 0 := by
    rw [eval_intersection _ _ _ hikp]
    exact div_ne_zero (no_concurrent_at_pair n L hs ⟨t.i,hin⟩ ⟨t.k,hkn⟩ r
      (show t.i < t.k from lt_trans hij hjk) hri' hrk') hikp
  have hevjk : affineEval (L r) (intersection (L t.j) (L t.k)) ≠ 0 := by
    rw [eval_intersection _ _ _ hjkp]
    exact div_ne_zero (no_concurrent_at_pair n L hs ⟨t.j,hjn⟩ ⟨t.k,hkn⟩ r hjk hrj' hrk') hjkp
  have hsign := htri r
  rw [oriented_nonneg_iff _ _ _ hijp,oriented_nonneg_iff _ _ _ hikp,
    oriented_nonneg_iff _ _ _ hjkp,oriented_nonpos_iff _ _ _ hijp,
    oriented_nonpos_iff _ _ _ hikp,oriented_nonpos_iff _ _ _ hjkp] at hsign
  have hall : ∀ᶠ κ in 𝓝 (0:ℝ), ∀ s : Fin m, weakSigns
      (affineEval (perturb (L r) (D s) κ) (intersection (L t.i) (L t.j)))
      (affineEval (perturb (L r) (D s) κ) (intersection (L t.i) (L t.k)))
      (affineEval (perturb (L r) (D s) κ) (intersection (L t.j) (L t.k))) := by
    apply Filter.eventually_all.mpr
    intro s
    exact triangle_test_eventually _ _ _ _ _ hsign hevij hevik hevjk
  apply hall.mono
  intro κ hκ
  refine ⟨hij,hjk,by omega,?_,?_⟩
  · simpa [pencilAppend,hin,hjn,hkn] using hnd
  intro s
  by_cases hsn : s.val < n
  · simpa [pencilAppend,hin,hjn,hkn,hsn] using htri ⟨s.val,hsn⟩
  · have hsm : s.val-n < m := by omega
    simp only [pencilAppend,if_pos hin,if_pos hjn,if_pos hkn,if_neg hsn]
    rw [oriented_nonneg_iff _ _ _ hijp,oriented_nonneg_iff _ _ _ hikp,
      oriented_nonneg_iff _ _ _ hjkp,oriented_nonpos_iff _ _ _ hijp,
      oriented_nonpos_iff _ _ _ hikp,oriented_nonpos_iff _ _ _ hjkp]
    exact hκ ⟨s.val-n,hsm⟩

#print axioms triangle_preserved_eventually
end Kobon.BBLPersistence
