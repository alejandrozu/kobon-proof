import Kobon.BBLPencilProfiles

/-! Nonparallel directions and a positive choice of the BBL perturbation.
The good perturbation is obtained from actual crossing profiles, not from
an assumed arrangement or assumed triangle count. -/
namespace Kobon.BBLPencilRegularity
open Real BBLAnalytic BBLGrid BBLGridCuts BBLIntersection BBLPencilLimits
  BBLPencilProfiles BBLProfiles BBLLiftedKeys Filter
open scoped Topology

theorem positive_eventually_exists (P : ℝ → Prop)
    (h : ∀ᶠ x in 𝓝 (0:ℝ), 0 < x → P x) : ∃ x : ℝ, 0 < x ∧ P x := by
  obtain ⟨η,hη,hP⟩ := Metric.eventually_nhds_iff.mp h
  refine ⟨η/2,by positivity,?_⟩
  apply hP
  · simp only [Real.dist_eq,sub_zero,abs_of_pos (by positivity : 0 < η/2)]
    linarith
  · positivity

theorem pairDen_eventually_ne (t u : ℝ) (ht : t ≠ 0) (hu : u ≠ 0) :
    ∀ᶠ δ in 𝓝 (0:ℝ), 0 < δ → pairDen δ t u ≠ 0 := by
  by_cases hp : t*u = 1
  · apply Filter.Eventually.of_forall
    intro δ hδ
    have heq : pairDen δ t u = -(δ*(1+t^2)*(1+u^2)) := by
      unfold pairDen
      rw [hp]
      ring
    rw [heq]
    exact neg_ne_zero.mpr (ne_of_gt (mul_pos (mul_pos hδ (one_add_sq_pos t))
      (one_add_sq_pos u)))
  · have hc : ContinuousAt (fun δ => pairDen δ t u) 0 := by unfold pairDen; fun_prop
    exact (hc.eventually_ne (pairDen_zero_ne t u ht hu (by intro h; apply hp; linarith))).mono
      (fun _ hh _ => hh)

theorem factor_pos (δ t : ℝ) (hδ : 0 < δ) (ht : 0 < t) : 0 < slopeFactor δ t := by
  unfold slopeFactor
  exact add_pos (div_pos (by positivity) (one_add_sq_pos t)) (div_pos hδ ht)

theorem factor_neg (δ t : ℝ) (hδ : 0 < δ) (ht : t < 0) : slopeFactor δ t < 0 := by
  unfold slopeFactor
  exact add_neg (div_neg_of_neg_of_pos (by linarith) (one_add_sq_pos t))
    (div_neg_of_pos_of_neg hδ ht)

theorem factor_ne (δ t : ℝ) (hδ : 0 < δ) (ht : t ≠ 0) : slopeFactor δ t ≠ 0 := by
  rcases lt_or_gt_of_ne ht with h | h
  · exact ne_of_lt (factor_neg δ t hδ h)
  · exact ne_of_gt (factor_pos δ t hδ h)

theorem factors_distinct (δ t u : ℝ) (ht : t ≠ 0) (hu : u ≠ 0)
    (htu : t ≠ u) (hd : pairDen δ t u ≠ 0) : slopeFactor δ t ≠ slopeFactor δ u := by
  apply sub_ne_zero.mp
  rw [factor_difference δ t u ht hu]
  exact div_ne_zero (mul_ne_zero (sub_ne_zero.mpr htu) hd)
    (mul_ne_zero (mul_ne_zero (mul_ne_zero ht hu) (ne_of_gt (one_add_sq_pos t)))
      (ne_of_gt (one_add_sq_pos u)))

def GoodDelta (r : Nat) (ε δ : ℝ) : Prop :=
  0 < δ ∧ ∀ i k : Fin (4*r), i ≠ k →
    pairDen δ (tan (beta r i)) (tan (beta r k)) ≠ 0 ∧
    Profile (8*(r:Int)) (cut r ε) (liftedNewKey (2*(r:Int)) i.val k.val)
      (pairX δ (tan (beta r i)) (tan (beta r k)))

theorem good_delta_eventually (r : Nat) (hr : 5 ≤ r) (ε : ℝ)
    (hε0 : 0 < ε) (hε : ε < tan (alpha r/2)) :
    ∀ᶠ δ in 𝓝 (0:ℝ), 0<δ → GoodDelta r ε δ := by
  have hall : ∀ᶠ δ in 𝓝 (0:ℝ), ∀ i k : Fin (4*r), i ≠ k → 0 < δ →
      pairDen δ (tan (beta r i)) (tan (beta r k)) ≠ 0 ∧
      Profile (8*(r:Int)) (cut r ε) (liftedNewKey (2*(r:Int)) i.val k.val)
        (pairX δ (tan (beta r i)) (tan (beta r k))) := by
    apply Filter.eventually_all.mpr
    intro i
    apply Filter.eventually_all.mpr
    intro k
    by_cases hik : i ≠ k
    · have hd := pairDen_eventually_ne _ _ (beta_tan_ne_zero r hr i) (beta_tan_ne_zero r hr k)
      have hp := pair_profile_eventually r hr ε hε0 hε i k hik
      exact (hd.and hp).mono (fun δ hδ _ hδp => ⟨hδ.1 hδp,hδ.2 hδp⟩)
    · exact Filter.Eventually.of_forall (fun _ hh => (hik hh).elim)
  exact hall.mono (fun δ hgood hδ => ⟨hδ,fun i k hik => hgood i k hik hδ⟩)

theorem good_delta_exists (r : Nat) (hr : 5 ≤ r) (ε : ℝ)
    (hε0 : 0 < ε) (hε : ε < tan (alpha r/2)) : ∃ δ, GoodDelta r ε δ := by
  obtain ⟨δ,_,hδ⟩ := positive_eventually_exists _ (good_delta_eventually r hr ε hε0 hε)
  exact ⟨δ,hδ⟩

#print axioms good_delta_exists
end Kobon.BBLPencilRegularity
