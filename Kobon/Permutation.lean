import Kobon.Reindex
import Mathlib.Data.List.Nodup

/-! Relabeling arrangements preserves their actual triangle witnesses.
The sorting operation is only on line labels; no geometric deformation is used.
-/
namespace Kobon.Permutation
open Reindex BBLTriangles

def Shape (n : Nat) (L : Nat → Line ℝ) (a b c : Nat) : Prop :=
  evalVertex (L c) (L a) (L b) ≠ 0 ∧
  ∀ r : Fin n,
    (0 ≤ orientedEval (L r) (L a) (L b) ∧
      0 ≤ orientedEval (L r) (L a) (L c) ∧
      0 ≤ orientedEval (L r) (L b) (L c)) ∨
    (orientedEval (L r) (L a) (L b) ≤ 0 ∧
      orientedEval (L r) (L a) (L c) ≤ 0 ∧
      orientedEval (L r) (L b) (L c) ≤ 0)

theorem shape_swap (n : Nat) (L : Nat → Line ℝ) (a b c : Nat)
    (h : Shape n L a b c) : Shape n L b a c := by
  refine ⟨?_,?_⟩
  · rw [eval_pair_swap]
    exact neg_ne_zero.mpr h.1
  · intro r
    rw [oriented_swap (L r) (L b) (L a)]
    rcases h.2 r with hr | hr
    · exact Or.inl ⟨hr.1,hr.2.2,hr.2.1⟩
    · exact Or.inr ⟨hr.1,hr.2.2,hr.2.1⟩

theorem shape_rotate (n : Nat) (L : Nat → Line ℝ) (a b c : Nat)
    (h : Shape n L a b c) : Shape n L b c a := by
  refine ⟨?_,?_⟩
  · simpa only [eval_cyclic (L a) (L b) (L c)] using h.1
  · intro r
    rw [oriented_swap (L r) (L b) (L a),oriented_swap (L r) (L c) (L a)]
    rcases h.2 r with hr | hr
    · exact Or.inl ⟨hr.2.2,hr.1,hr.2.1⟩
    · exact Or.inr ⟨hr.2.2,hr.1,hr.2.1⟩

def sortTriple (a b c : Nat) : Triple :=
  if a < b then
    if b < c then ⟨a,b,c⟩ else if a < c then ⟨a,c,b⟩ else ⟨c,a,b⟩
  else
    if a < c then ⟨b,a,c⟩ else if b < c then ⟨b,c,a⟩ else ⟨c,b,a⟩

theorem sortTriple_sorted (a b c : Nat) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    (sortTriple a b c).i < (sortTriple a b c).j ∧
      (sortTriple a b c).j < (sortTriple a b c).k := by
  unfold sortTriple
  split_ifs <;> dsimp <;> omega

theorem sortTriple_mem (a b c x : Nat) :
    (x=(sortTriple a b c).i ∨ x=(sortTriple a b c).j ∨ x=(sortTriple a b c).k) ↔
      (x=a ∨ x=b ∨ x=c) := by
  unfold sortTriple
  split_ifs <;> dsimp <;> tauto

theorem shape_sort (n : Nat) (L : Nat → Line ℝ) (a b c : Nat)
    (h : Shape n L a b c) :
    Shape n L (sortTriple a b c).i (sortTriple a b c).j (sortTriple a b c).k := by
  have hs := shape_swap n L a b c h
  have hr := shape_rotate n L a b c h
  have hrr := shape_rotate n L b c a hr
  have hsr := shape_rotate n L b a c hs
  have hrs := shape_swap n L b c a hr
  unfold sortTriple
  split_ifs <;> dsimp <;> assumption

theorem triangle_pullback_support (N M : Nat) (L : Nat → Line ℝ) (f : Nat → Nat)
    (hf : ∀ r : Fin M, f r < N) (t : Triple) (ht : TrianglePredicate N L t)
    (a b c : Nat) (hab : a < b) (hbc : b < c) (hc : c < M)
    (hsupp : ∀ x, (x=f a ∨ x=f b ∨ x=f c) ↔ (x=t.i ∨ x=t.j ∨ x=t.k)) :
    TrianglePredicate M (fun r => L (f r)) ⟨a,b,c⟩ := by
  have ha := (hsupp (f a)).mp (Or.inl rfl)
  have hb := (hsupp (f b)).mp (Or.inr (Or.inl rfl))
  have hd := (hsupp (f c)).mp (Or.inr (Or.inr rfl))
  have hi := (hsupp t.i).mpr (Or.inl rfl)
  have hj := (hsupp t.j).mpr (Or.inr (Or.inl rfl))
  have hk := (hsupp t.k).mpr (Or.inr (Or.inr rfl))
  have hij := ht.1
  have hjk := ht.2.1
  have hshape : Shape N L t.i t.j t.k := ⟨ht.2.2.2.1,ht.2.2.2.2⟩
  have hs := shape_swap N L t.i t.j t.k hshape
  have hr := shape_rotate N L t.i t.j t.k hshape
  have hrr := shape_rotate N L t.j t.k t.i hr
  have hsr := shape_rotate N L t.j t.i t.k hs
  have hrs := shape_swap N L t.j t.k t.i hr
  have hp : Shape N L (f a) (f b) (f c) := by
    rcases ha with ha | ha | ha <;> rcases hb with hb | hb | hb <;>
      rcases hd with hd | hd | hd <;> try omega
    all_goals simp only [ha,hb,hd]; assumption
  exact ⟨hab,hbc,hc,hp.1,fun r => hp.2 ⟨f r,hf r⟩⟩

def relabelTriple (g : Nat → Nat) (t : Triple) : Triple :=
  sortTriple (g t.i) (g t.j) (g t.k)

theorem sorted_triple_ext (t u : Triple)
    (ht : t.i < t.j ∧ t.j < t.k) (hu : u.i < u.j ∧ u.j < u.k)
    (h : ∀ x, (x=t.i ∨ x=t.j ∨ x=t.k) ↔ (x=u.i ∨ x=u.j ∨ x=u.k)) : t=u := by
  have hti := (h t.i).mp (Or.inl rfl)
  have htj := (h t.j).mp (Or.inr (Or.inl rfl))
  have htk := (h t.k).mp (Or.inr (Or.inr rfl))
  have hui := (h u.i).mpr (Or.inl rfl)
  have huj := (h u.j).mpr (Or.inr (Or.inl rfl))
  have huk := (h u.k).mpr (Or.inr (Or.inr rfl))
  have hi : t.i=u.i := by omega
  have hj : t.j=u.j := by omega
  have hk : t.k=u.k := by omega
  cases t; cases u
  simp_all

theorem relabel_support (N : Nat) (f g : Nat → Nat)
    (hfg : ∀ x, x<N → f (g x)=x) (t : Triple)
    (hti : t.i<N) (htj : t.j<N) (htk : t.k<N) (x : Nat) :
    (x=f (relabelTriple g t).i ∨ x=f (relabelTriple g t).j ∨ x=f (relabelTriple g t).k) ↔
      (x=t.i ∨ x=t.j ∨ x=t.k) := by
  unfold relabelTriple sortTriple
  split_ifs <;> dsimp <;> rw [hfg t.i hti,hfg t.j htj,hfg t.k htk] <;> tauto

theorem relabel_triangle (N : Nat) (L : Nat → Line ℝ) (f g : Nat → Nat)
    (hf : ∀ r : Fin N, f r<N) (hg : ∀ x, x<N → g x<N)
    (hfg : ∀ x, x<N → f (g x)=x) (t : Triple) (ht : TrianglePredicate N L t) :
    TrianglePredicate N (fun r => L (f r)) (relabelTriple g t) := by
  have hti : t.i<N := by have := ht.1; have := ht.2.1; have := ht.2.2.1; omega
  have htj : t.j<N := by have := ht.2.1; have := ht.2.2.1; omega
  have htk : t.k<N := ht.2.2.1
  have hgi : g t.i ≠ g t.j := by
    intro h
    have hh := congrArg f h
    rw [hfg t.i hti,hfg t.j htj] at hh
    have := ht.1
    omega
  have hgk : g t.i ≠ g t.k := by
    intro h
    have hh := congrArg f h
    rw [hfg t.i hti,hfg t.k htk] at hh
    have := ht.1; have := ht.2.1
    omega
  have hgj : g t.j ≠ g t.k := by
    intro h
    have hh := congrArg f h
    rw [hfg t.j htj,hfg t.k htk] at hh
    have := ht.2.1
    omega
  have ho := sortTriple_sorted (g t.i) (g t.j) (g t.k) hgi hgk hgj
  have hb : (relabelTriple g t).k<N := by
    have hi := hg t.i hti
    have hj := hg t.j htj
    have hk := hg t.k htk
    unfold relabelTriple sortTriple
    split_ifs <;> dsimp <;> assumption
  exact triangle_pullback_support N N L f hf t ht
    (relabelTriple g t).i (relabelTriple g t).j (relabelTriple g t).k ho.1 ho.2 hb
    (relabel_support N f g hfg t hti htj htk)

theorem relabel_injective (N : Nat) (f g : Nat → Nat)
    (hfg : ∀ x, x<N → f (g x)=x) (t u : Triple)
    (ht : t.i < t.j ∧ t.j < t.k ∧ t.k<N)
    (hu : u.i < u.j ∧ u.j < u.k ∧ u.k<N)
    (h : relabelTriple g t=relabelTriple g u) : t=u := by
  apply sorted_triple_ext t u ⟨ht.1,ht.2.1⟩ ⟨hu.1,hu.2.1⟩
  intro x
  rw [← relabel_support N f g hfg t (by omega) (by omega) ht.2.2 x,
    ← relabel_support N f g hfg u (by omega) (by omega) hu.2.2 x,h]

/-- Every witness list transports with exactly the same length. -/
theorem transport_list (N : Nat) (L : Nat → Line ℝ) (f g : Nat → Nat)
    (hf : ∀ r : Fin N, f r<N) (hg : ∀ x, x<N → g x<N)
    (hfg : ∀ x, x<N → f (g x)=x)
    (ts : List Triple) (hn : ts.Nodup)
    (ht : ∀ t∈ts, TrianglePredicate N L t) :
    ∃ us : List Triple, us.Nodup ∧
      (∀ u∈us, TrianglePredicate N (fun r => L (f r)) u) ∧ us.length=ts.length := by
  refine ⟨ts.map (relabelTriple g),List.Nodup.map_on ?_ hn,?_,by simp⟩
  · intro t htm u hum he
    have hT := ht t htm
    have hU := ht u hum
    exact relabel_injective N f g hfg t u ⟨hT.1,hT.2.1,hT.2.2.1⟩
      ⟨hU.1,hU.2.1,hU.2.2.1⟩ he
  · intro u hu
    obtain ⟨t,htm,rfl⟩ := List.mem_map.mp hu
    exact relabel_triangle N L f g hf hg hfg t (ht t htm)

#print axioms triangle_pullback_support
#print axioms transport_list

/-- Bounded injectivity suffices: a finite permutation has a bounded inverse. -/
theorem transport_list_of_injective (N : Nat) (L : Nat → Line ℝ) (f : Nat → Nat)
    (hf : ∀ r : Fin N, f r<N)
    (hinj : ∀ i j : Fin N, f i=f j → i=j)
    (ts : List Triple) (hn : ts.Nodup)
    (ht : ∀ t∈ts, TrianglePredicate N L t) :
    ∃ us : List Triple, us.Nodup ∧
      (∀ u∈us, TrianglePredicate N (fun r => L (f r)) u) ∧ us.length=ts.length := by
  classical
  let F : Fin N → Fin N := fun i => ⟨f i,hf i⟩
  have hF : Function.Injective F := by
    intro i j h
    exact hinj i j (congrArg Fin.val h)
  have hsurj := Finite.surjective_of_injective hF
  let e : Fin N ≃ Fin N := Equiv.ofBijective F ⟨hF,hsurj⟩
  let g : Nat → Nat := fun x => if hx : x<N then (e.symm ⟨x,hx⟩).val else 0
  have hg : ∀ x, x<N → g x<N := by
    intro x hx
    simpa only [g,dif_pos hx] using (e.symm ⟨x,hx⟩).isLt
  have hfg : ∀ x, x<N → f (g x)=x := by
    intro x hx
    have hh := congrArg Fin.val (e.apply_symm_apply ⟨x,hx⟩)
    simpa only [g,dif_pos hx,e,Equiv.ofBijective_apply,F] using hh
  exact transport_list N L f g hf hg hfg ts hn ht

#print axioms transport_list_of_injective

theorem triangle_congr (N : Nat) (L M : Nat → Line ℝ)
    (hLM : ∀ i, i<N → L i=M i) (t : Triple) (ht : TrianglePredicate N L t) :
    TrianglePredicate N M t := by
  have hi : t.i<N := by have := ht.1; have := ht.2.1; have := ht.2.2.1; omega
  have hj : t.j<N := by have := ht.2.1; have := ht.2.2.1; omega
  have hk : t.k<N := ht.2.2.1
  refine ⟨ht.1,ht.2.1,hk,?_,?_⟩
  · simpa only [← hLM t.i hi,← hLM t.j hj,← hLM t.k hk] using ht.2.2.2.1
  · intro r
    simpa only [← hLM t.i hi,← hLM t.j hj,← hLM t.k hk,← hLM r r.isLt]
      using ht.2.2.2.2 r

theorem no_parallel_congr (N : Nat) (L M : Nat → Line ℝ)
    (hLM : ∀ i, i<N → L i=M i) (hp : NoParallel N L) : NoParallel N M := by
  intro i j hij
  simpa only [← hLM i i.isLt,← hLM j j.isLt] using hp i j hij

theorem no_concurrent_congr (N : Nat) (L M : Nat → Line ℝ)
    (hLM : ∀ i, i<N → L i=M i) (hs : NoConcurrent N L) : NoConcurrent N M := by
  intro i j k hij hjk
  simpa only [← hLM i i.isLt,← hLM j j.isLt,← hLM k k.isLt] using hs i j k hij hjk

end Kobon.Permutation
