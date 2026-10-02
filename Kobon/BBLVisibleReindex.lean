import Kobon.Permutation

/-! Exact relabeling of visible pairs and their finite certificates. -/
namespace Kobon.BBLVisibleReindex
open Exterior
set_option autoImplicit false

theorem visible_pullback_support (N M : Nat) (L : Nat → Line ℝ) (w : Line ℝ)
    (f : Nat → Nat) (hf : ∀ r : Fin M, f r<N)
    (t : Triple) (ht : VisiblePair N L w t)
    (a b : Nat) (hab : a<b) (hb : b<M)
    (hsupp : ∀ x, (x=f a ∨ x=f b) ↔ (x=t.i ∨ x=t.j)) :
    VisiblePair M (fun r => L (f r)) w ⟨a,b,M⟩ := by
  have ha := (hsupp (f a)).mp (Or.inl rfl)
  have hb' := (hsupp (f b)).mp (Or.inr rfl)
  have hi := (hsupp t.i).mpr (Or.inl rfl)
  have hj := (hsupp t.j).mpr (Or.inr rfl)
  have hij := ht.1
  refine ⟨hab,hb,rfl,?_⟩
  intro r
  have hr := ht.2.2.2 ⟨f r,hf r⟩
  rcases ha with ha | ha <;> rcases hb' with hb' | hb' <;> try omega
  · simpa only [ha,hb'] using hr
  · simp only [ha,hb',intersection_swap (L t.j) (L t.i)]
    rcases hr with hr | hr
    · exact Or.inl ⟨hr.1,hr.2.2,hr.2.1⟩
    · exact Or.inr ⟨hr.1,hr.2.2,hr.2.1⟩

def pairRelabel (N : Nat) (g : Nat → Nat) (t : Triple) : Triple :=
  if g t.i<g t.j then ⟨g t.i,g t.j,N⟩ else ⟨g t.j,g t.i,N⟩

theorem pair_restore (N : Nat) (f g : Nat → Nat)
    (hfg : ∀ x, x<N → f (g x)=x) (t : Triple)
    (hij : t.i<t.j) (hj : t.j<N) (hk : t.k=N) :
    pairRelabel N f (pairRelabel N g t)=t := by
  have hi : t.i<N := by omega
  cases t with
  | mk i j k =>
    dsimp at *
    subst k
    by_cases h : g i<g j
    · simp [pairRelabel,h,hfg i hi,hfg j hj,hij]
    · simp [pairRelabel,h,hfg i hi,hfg j hj,show ¬ (j < i) by omega]

theorem relabel_visible (N : Nat) (L : Nat → Line ℝ) (w : Line ℝ) (f g : Nat → Nat)
    (hf : ∀ r : Fin N, f r<N) (hg : ∀ x, x<N → g x<N)
    (hfg : ∀ x, x<N → f (g x)=x) (t : Triple) (ht : VisiblePair N L w t) :
    VisiblePair N (fun r => L (f r)) w (pairRelabel N g t) := by
  have hij := ht.1
  have hj := ht.2.1
  have hi : t.i<N := by omega
  have hne : g t.i≠g t.j := by
    intro h
    have he := congrArg f h
    rw [hfg t.i hi,hfg t.j hj] at he
    omega
  unfold pairRelabel
  split_ifs with h
  · apply visible_pullback_support N N L w f hf t ht (g t.i) (g t.j) h (hg t.j hj)
    intro x
    simp only [hfg t.i hi,hfg t.j hj]
  · apply visible_pullback_support N N L w f hf t ht (g t.j) (g t.i) (by omega) (hg t.i hi)
    intro x
    simp only [hfg t.i hi,hfg t.j hj]
    tauto

theorem transport_list (N : Nat) (L : Nat → Line ℝ) (w : Line ℝ) (f g : Nat → Nat)
    (hf : ∀ r : Fin N, f r<N) (hg : ∀ x, x<N → g x<N)
    (hfg : ∀ x, x<N → f (g x)=x)
    (vs : List Triple) (hn : vs.Nodup) (hv : ∀ t∈vs, VisiblePair N L w t) :
    ∃ us : List Triple, us.Nodup ∧
      (∀ t∈us, VisiblePair N (fun r => L (f r)) w t) ∧ us.length=vs.length := by
  refine ⟨vs.map (pairRelabel N g),List.Nodup.map_on ?_ hn,?_,by simp⟩
  · intro t htm u hum he
    have ht := hv t htm
    have hu := hv u hum
    have hh := congrArg (pairRelabel N f) he
    simpa only [pair_restore N f g hfg t ht.1 ht.2.1 ht.2.2.1,
      pair_restore N f g hfg u hu.1 hu.2.1 hu.2.2.1] using hh
  · intro t htm
    obtain ⟨u,hum,rfl⟩ := List.mem_map.mp htm
    exact relabel_visible N L w f g hf hg hfg u (hv u hum)

theorem transport_list_of_injective (N : Nat) (L : Nat → Line ℝ) (w : Line ℝ)
    (f : Nat → Nat) (hf : ∀ r : Fin N, f r<N)
    (hinj : ∀ i j : Fin N, f i=f j → i=j)
    (vs : List Triple) (hn : vs.Nodup) (hv : ∀ t∈vs, VisiblePair N L w t) :
    ∃ us : List Triple, us.Nodup ∧
      (∀ t∈us, VisiblePair N (fun r => L (f r)) w t) ∧ us.length=vs.length := by
  classical
  let F : Fin N → Fin N := fun i => ⟨f i,hf i⟩
  have hF : Function.Injective F := by
    intro i j h
    exact hinj i j (congrArg Fin.val h)
  let e : Fin N ≃ Fin N := Equiv.ofBijective F ⟨hF,Finite.surjective_of_injective hF⟩
  let g : Nat → Nat := fun x => if hx : x<N then (e.symm ⟨x,hx⟩).val else 0
  have hg : ∀ x, x<N → g x<N := by
    intro x hx
    simpa only [g,dif_pos hx] using (e.symm ⟨x,hx⟩).isLt
  have hfg : ∀ x, x<N → f (g x)=x := by
    intro x hx
    have hh := congrArg Fin.val (e.apply_symm_apply ⟨x,hx⟩)
    simpa only [g,dif_pos hx,e,Equiv.ofBijective_apply,F] using hh
  exact transport_list N L w f g hf hg hfg vs hn hv

theorem visible_congr (N : Nat) (L M : Nat → Line ℝ) (w : Line ℝ)
    (hLM : ∀ i, i<N → L i=M i) (t : Triple) (ht : VisiblePair N L w t) :
    VisiblePair N M w t := by
  have hi : t.i<N := by have := ht.1; have := ht.2.1; omega
  have hj := ht.2.1
  refine ⟨ht.1,hj,ht.2.2.1,?_⟩
  intro r
  simpa only [← hLM t.i hi,← hLM t.j hj,← hLM r r.isLt] using ht.2.2.2 r

theorem admissible_pullback (N M : Nat) (L : Nat → Line ℝ) (w : Line ℝ)
    (f : Nat → Nat) (hf : ∀ r : Fin M, f r<N) (hw : Admissible N L w) :
    Admissible M (fun r => L (f r)) w := fun r => hw ⟨f r,hf r⟩

theorem admissible_congr (N : Nat) (L M : Nat → Line ℝ) (w : Line ℝ)
    (hLM : ∀ i, i<N → L i=M i) (hw : Admissible N L w) : Admissible N M w := by
  intro i
  simpa only [← hLM i i.isLt] using hw i

#print axioms transport_list
#print axioms transport_list_of_injective
end Kobon.BBLVisibleReindex
