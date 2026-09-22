import Kobon.BBLPersistence

/-! A small near-horizontal pencil is transverse to every old line. Distinct
nonzero pencil slope factors then make the entire enlarged arrangement
pairwise nonparallel at every sufficiently small nonzero scale. -/
namespace Kobon.BBLRegularity
open BBLExtrema BBLPersistence Filter
open scoped Topology

noncomputable def canonical (q : Nat) (m a v b : Nat → ℝ) (κ : ℝ) (i : Nat) : Line ℝ :=
  if i<q then graphLine (m i) (a i)
  else if i<2*q then graphLine (κ*v (i-q)) (b (i-q))
  else graphLine 0 0

theorem det_graph (m a s b : ℝ) : det (graphLine m a) (graphLine s b)=s-m := by
  dsimp [det,graphLine]
  ring

theorem old_new_eventually (q : Nat) (m v : Nat → ℝ)
    (hm : ∀ i : Fin q, m i≠0) :
    ∀ᶠ κ in 𝓝 (0:ℝ), ∀ i j : Fin q, κ*v j-m i≠0 := by
  apply Filter.eventually_all.mpr
  intro i
  apply Filter.eventually_all.mpr
  intro j
  have hc : ContinuousAt (fun κ => m i*(m i-κ*v j)) 0 := by fun_prop
  have hp : 0<m i*(m i-(0:ℝ)*v j) := by simpa [pow_two] using sq_pos_of_ne_zero (hm i)
  exact (Filter.Tendsto.eventually_const_lt hp hc).mono (by
    intro κ hκ he
    have hh : m i-κ*v j=0 := by linarith
    rw [hh,mul_zero] at hκ
    exact (lt_irrefl 0) hκ)

theorem canonical_no_parallel_eventually (q : Nat) (m a v b : Nat → ℝ)
    (hm : ∀ i : Fin q, m i≠0) (hv : ∀ i : Fin q, v i≠0)
    (hmij : ∀ i j : Fin q, i<j → m i≠m j)
    (hvij : ∀ i j : Fin q, i<j → v i≠v j) :
    ∀ᶠ κ in 𝓝 (0:ℝ), κ≠0 → NoParallel (2*q+1) (canonical q m a v b κ) := by
  apply (old_new_eventually q m v hm).mono
  intro κ hκ hk i j hij
  have hijv : i.val<j.val := hij
  by_cases hjold : j.val<q
  · have hiold : i.val<q := by omega
    simp only [canonical,if_pos hiold,if_pos hjold,det_graph]
    exact sub_ne_zero.mpr (Ne.symm (hmij ⟨i.val,hiold⟩ ⟨j.val,hjold⟩ hij))
  by_cases hiold : i.val<q
  · by_cases hjnew : j.val<2*q
    · have hjq : j.val-q<q := by omega
      simp only [canonical,if_pos hiold,if_neg hjold,if_pos hjnew,det_graph]
      exact hκ ⟨i.val,hiold⟩ ⟨j.val-q,hjq⟩
    · simp only [canonical,if_pos hiold,if_neg hjold,if_neg hjnew,det_graph,zero_sub]
      exact neg_ne_zero.mpr (hm ⟨i.val,hiold⟩)
  · have hinew : i.val<2*q := by omega
    have hiq : i.val-q<q := by omega
    by_cases hjnew : j.val<2*q
    · have hjq : j.val-q<q := by omega
      simp only [canonical,if_neg hiold,if_pos hinew,if_neg hjold,if_pos hjnew,det_graph]
      have hdiff : v (j.val-q)-v (i.val-q)≠0 :=
        sub_ne_zero.mpr (Ne.symm (hvij ⟨i.val-q,hiq⟩ ⟨j.val-q,hjq⟩
          (show i.val-q<j.val-q by omega)))
      rw [← mul_sub]
      exact mul_ne_zero hk hdiff
    · simp only [canonical,if_neg hiold,if_pos hinew,if_neg hjold,if_neg hjnew,det_graph,zero_sub]
      exact neg_ne_zero.mpr (mul_ne_zero hk (hv ⟨i.val-q,hiq⟩))

#print axioms canonical_no_parallel_eventually
end Kobon.BBLRegularity
