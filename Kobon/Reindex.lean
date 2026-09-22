import Kobon.BBLTriangles

/-! Reindexing actual arrangements, including the cyclic move that puts the
distinguished line last in the BBL crossing-order model. -/
namespace Kobon.Reindex
open BBLTriangles BBLExtrema

theorem oriented_swap (r l m : Line ℝ) : orientedEval r l m=orientedEval r m l := by
  dsimp [orientedEval,evalVertex,vertex,det]
  ring

theorem eval_pair_swap (r l m : Line ℝ) : evalVertex r l m= -evalVertex r m l := by
  dsimp [evalVertex,vertex,det]
  ring

theorem triangle_pullback (N M : Nat) (L : Nat → Line ℝ) (f : Nat → Nat)
    (hf : ∀ r : Fin M, f r<N) (t : Triple) (ht : TrianglePredicate N L t)
    (a b c : Nat) (hab : a<b) (hbc : b<c) (hc : c<M)
    (ha : f a=t.i) (hb : f b=t.j) (hk : f c=t.k) :
    TrianglePredicate M (fun r => L (f r)) ⟨a,b,c⟩ := by
  refine ⟨hab,hbc,hc,?_,?_⟩
  · simpa [ha,hb,hk] using ht.2.2.2.1
  · intro r
    simpa [ha,hb,hk] using ht.2.2.2.2 ⟨f r,hf r⟩

theorem triangle_cyclic_pullback (N M : Nat) (L : Nat → Line ℝ) (f : Nat → Nat)
    (hf : ∀ r : Fin M, f r<N) (t : Triple) (ht : TrianglePredicate N L t)
    (a b c : Nat) (hab : a<b) (hbc : b<c) (hc : c<M)
    (ha : f a=t.j) (hb : f b=t.k) (hk : f c=t.i) :
    TrianglePredicate M (fun r => L (f r)) ⟨a,b,c⟩ := by
  refine ⟨hab,hbc,hc,?_,?_⟩
  · simpa [ha,hb,hk,eval_cyclic (L t.i) (L t.j) (L t.k)] using ht.2.2.2.1
  · intro r
    simp only [ha,hb,hk]
    rw [oriented_swap (L (f r)) (L t.j) (L t.i),oriented_swap (L (f r)) (L t.k) (L t.i)]
    rcases ht.2.2.2.2 ⟨f r,hf r⟩ with h | h
    · exact Or.inl ⟨h.2.2,h.1,h.2.1⟩
    · exact Or.inr ⟨h.2.2,h.1,h.2.1⟩

theorem no_parallel_pullback (N M : Nat) (L : Nat → Line ℝ) (f : Nat → Nat)
    (hf : ∀ r : Fin M, f r<N)
    (hinj : ∀ i j : Fin M, f i=f j → i=j) (hp : NoParallel N L) :
    NoParallel M (fun r => L (f r)) := by
  intro i j hij
  apply det_ne_of_ne N L hp ⟨f i,hf i⟩ ⟨f j,hf j⟩
  intro he
  have hh := hinj i j (congrArg Fin.val he)
  subst j
  exact (lt_irrefl i) hij

theorem no_concurrent_pullback (N M : Nat) (L : Nat → Line ℝ) (f : Nat → Nat)
    (hf : ∀ r : Fin M, f r<N)
    (hinj : ∀ i j : Fin M, f i=f j → i=j) (hs : NoConcurrent N L) :
    NoConcurrent M (fun r => L (f r)) := by
  intro i j k hij hjk
  have hfi : f k≠f i := by intro h; have hh := hinj k i h; subst k; omega
  have hfj : f k≠f j := by intro h; have hh := hinj k j h; subst k; omega
  have hfij : f i≠f j := by intro h; have hh := hinj i j h; subst j; omega
  have hki : (⟨f k,hf k⟩ : Fin N)≠⟨f i,hf i⟩ := by intro h; exact hfi (congrArg Fin.val h)
  have hkj : (⟨f k,hf k⟩ : Fin N)≠⟨f j,hf j⟩ := by intro h; exact hfj (congrArg Fin.val h)
  rcases lt_or_gt_of_ne hfij with h | h
  · exact no_concurrent_at_pair N L hs ⟨f i,hf i⟩ ⟨f j,hf j⟩ ⟨f k,hf k⟩ h hki hkj
  · rw [eval_pair_swap]
    exact neg_ne_zero.mpr (no_concurrent_at_pair N L hs ⟨f j,hf j⟩ ⟨f i,hf i⟩ ⟨f k,hf k⟩ h hkj hki)

def shift (N x : Nat) : Nat := if x+1<N then x+1 else 0
def rotate (N : Nat) (L : Nat → Line ℝ) (x : Nat) : Line ℝ := L (shift N x)

theorem shift_bound (N : Nat) (hN : 0<N) (r : Fin N) : shift N r<N := by
  unfold shift
  split <;> omega

theorem shift_injective (N : Nat) (i j : Fin N) (h : shift N i=shift N j) : i=j := by
  apply Fin.ext
  unfold shift at h
  split_ifs at h <;> omega

theorem rotate_no_parallel (N : Nat) (hN : 0<N) (L : Nat → Line ℝ)
    (hp : NoParallel N L) : NoParallel N (rotate N L) :=
  no_parallel_pullback N N L (shift N) (shift_bound N hN) (shift_injective N) hp

theorem rotate_no_concurrent (N : Nat) (hN : 0<N) (L : Nat → Line ℝ)
    (hs : NoConcurrent N L) : NoConcurrent N (rotate N L) :=
  no_concurrent_pullback N N L (shift N) (shift_bound N hN) (shift_injective N) hs

theorem rotate_triangle (N : Nat) (L : Nat → Line ℝ) (t : Triple)
    (ht : TrianglePredicate N L t) (hti : 0<t.i) :
    TrianglePredicate N (rotate N L) ⟨t.i-1,t.j-1,t.k-1⟩ := by
  have hij := ht.1
  have hjk := ht.2.1
  have hkn := ht.2.2.1
  have hN : 0<N := by omega
  apply triangle_pullback N N L (shift N) (shift_bound N hN) t ht
    (t.i-1) (t.j-1) (t.k-1) (by omega) (by omega) (by omega)
  · simp [shift,show t.i-1+1=t.i by omega,show t.i<N by omega]
  · simp [shift,show t.j-1+1=t.j by omega,show t.j<N by omega]
  · simp [shift,show t.k-1+1=t.k by omega,hkn]

theorem rotate_zero_triangle (N i j : Nat) (L : Nat → Line ℝ)
    (ht : TrianglePredicate N L ⟨0,i,j⟩) :
    TrianglePredicate N (rotate N L) ⟨i-1,j-1,N-1⟩ := by
  have hi : 0 < i := ht.1
  have hij : i < j := ht.2.1
  have hjn : j < N := ht.2.2.1
  have hN : 0<N := by omega
  apply triangle_cyclic_pullback N N L (shift N) (shift_bound N hN) ⟨0,i,j⟩ ht
    (i-1) (j-1) (N-1) (by omega) (by omega) (by omega)
  · simp [shift,show i-1+1=i by omega,show i<N by omega]
  · simp [shift,show j-1+1=j by omega,hjn]
  · simp [shift,show N-1+1=N by omega]

theorem rotate_visible (N : Nat) (L : Nat → Line ℝ) (w : Line ℝ) (t : Triple)
    (ht : Exterior.VisiblePair N L w t) (hti : 0 < t.i) :
    Exterior.VisiblePair N (rotate N L) w ⟨t.i-1,t.j-1,N⟩ := by
  have hij := ht.1
  have hjn := ht.2.1
  have hiN : t.i < N := by omega
  have hN : 0 < N := by omega
  have hi : shift N (t.i-1)=t.i := by
    simp [shift,show t.i-1+1=t.i by omega,hiN]
  have hj : shift N (t.j-1)=t.j := by
    simp [shift,show t.j-1+1=t.j by omega,hjn]
  refine ⟨show t.i-1 < t.j-1 from by omega,show t.j-1 < N from by omega,rfl,?_⟩
  intro r
  simpa only [rotate,hi,hj] using ht.2.2.2 ⟨shift N r,shift_bound N hN r⟩

#print axioms rotate_visible
#print axioms rotate_triangle
#print axioms rotate_zero_triangle
#print axioms rotate_no_concurrent
end Kobon.Reindex
