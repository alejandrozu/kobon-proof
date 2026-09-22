import Kobon.BBLPersistence

/-! Strict order from intervals between a finite sequence of reference cuts.
This is the analytic-to-combinatorial interface for the BBL pencil. -/
namespace Kobon.BBLProfiles
open Filter
open scoped Topology

def IncreasingCuts (N : Int) (c : Int → ℝ) : Prop :=
  ∀ i j : Int, 0 ≤ i → j ≤ N → i < j → c i < c j

theorem IncreasingCuts.monotone {N : Int} {c : Int → ℝ} (hc : IncreasingCuts N c)
    (i j : Int) (hi : 0 ≤ i) (hj : j ≤ N) (hij : i ≤ j) : c i ≤ c j := by
  rcases lt_or_eq_of_le hij with h | h
  · exact le_of_lt (hc i j hi hj h)
  · rw [h]

/-- Even keys are exact cuts, odd keys lie in the intervening open intervals.
The two exceptional keys −1 and2N+1 describe unbounded exterior intervals. -/
def Profile (N : Int) (c : Int → ℝ) (key : Int) (x : ℝ) : Prop :=
  (key = -1 ∧ x < c 0) ∨
  (key = 2*N+1 ∧ c N < x) ∨
  (∃ j : Int, 0 ≤ j ∧ j ≤ N ∧ key = 2*j ∧ x = c j) ∨
  (∃ j : Int, 0 ≤ j ∧ j < N ∧ key = 2*j+1 ∧ c j < x ∧ x < c (j+1))

theorem profile_key_bounds (N : Int) (c : Int → ℝ) (key : Int) (x : ℝ)
    (hN : 0 ≤ N) (hp : Profile N c key x) : -1 ≤ key ∧ key ≤ 2*N+1 := by
  rcases hp with ⟨h,_⟩ | ⟨h,_⟩ | ⟨j,hj,hjN,h,_⟩ | ⟨j,hj,hjN,h,_⟩ <;> omega

theorem profile_strict_order (N : Int) (c : Int → ℝ) (hN : 0 ≤ N)
    (hc : IncreasingCuts N c) (k l : Int) (x y : ℝ)
    (hk : Profile N c k x) (hl : Profile N c l y) (hkl : k < l) : x < y := by
  have hbkl := profile_key_bounds N c l y hN hl
  rcases hk with ⟨hk,hx⟩ | ⟨hk,hx⟩ | ⟨i,hi,hiN,hk,hx⟩ | ⟨i,hi,hiN,hk,hix,hxi⟩
  · rcases hl with ⟨hl,hy⟩ | ⟨hl,hy⟩ | ⟨j,hj,hjN,hl,hy⟩ | ⟨j,hj,hjN,hl,hjy,hyj⟩
    · omega
    · have hcc := hc.monotone 0 N (le_refl _) (le_refl _) hN
      linarith
    · have hcc := hc.monotone 0 j (le_refl _) hjN hj
      linarith
    · have hcc := hc.monotone 0 j (le_refl _) (le_of_lt hjN) hj
      linarith
  · omega
  · rcases hl with ⟨hl,hy⟩ | ⟨hl,hy⟩ | ⟨j,hj,hjN,hl,hy⟩ | ⟨j,hj,hjN,hl,hjy,hyj⟩
    · omega
    · have hcc := hc.monotone i N hi (le_refl _) hiN
      linarith
    · have hcc := hc i j hi hjN (by omega)
      linarith
    · have hcc := hc.monotone i j hi (le_of_lt hjN) (by omega)
      linarith
  · rcases hl with ⟨hl,hy⟩ | ⟨hl,hy⟩ | ⟨j,hj,hjN,hl,hy⟩ | ⟨j,hj,hjN,hl,hjy,hyj⟩
    · omega
    · have hcc := hc.monotone (i+1) N (by omega) (le_refl _) (by omega)
      linarith
    · have hcc := hc.monotone (i+1) j (by omega) hjN (by omega)
      linarith
    · have hcc := hc.monotone (i+1) j (by omega) (le_of_lt hjN) (by omega)
      linarith

/-- Finitely many strict crossing comparisons survive a small scale change. -/
theorem finite_order_persistence {ι : Type} [Fintype ι] (key : ι → Int)
    (f : ι → ℝ → ℝ) (hc : ∀ i, ContinuousAt (f i) 0)
    (horder : ∀ i j, key i < key j → f i 0 < f j 0) :
    ∀ᶠ κ in 𝓝 (0:ℝ), ∀ i j, key i < key j → f i κ < f j κ := by
  apply Filter.eventually_all.mpr
  intro i
  apply Filter.eventually_all.mpr
  intro j
  by_cases hij : key i < key j
  · exact ((hc i).eventually_lt (hc j) (horder i j hij)).mono (fun _ h _ => h)
  · exact Filter.Eventually.of_forall (fun _ h => (hij h).elim)

theorem profile_left_eventually (N : Int) (c : Int → ℝ) (hc : IncreasingCuts N c)
    (j : Int) (hj : 1 ≤ j) (hjN : j ≤ N) (f : ℝ → ℝ)
    (hf : Tendsto f (𝓝 0) (𝓝 (c j)))
    (hside : ∀ᶠ δ in 𝓝 (0:ℝ), 0 < δ → f δ < c j) :
    ∀ᶠ δ in 𝓝 (0:ℝ), 0 < δ → Profile N c (2*j-1) (f δ) := by
  have hgap : c (j-1) < c j := hc (j-1) j (by omega) hjN (by omega)
  have hlo := Filter.Tendsto.eventually_const_lt hgap hf
  apply (hlo.and hside).mono
  intro δ hδ hδp
  right; right; right
  refine ⟨j-1,by omega,by omega,by omega,hδ.1,?_⟩
  simpa using hδ.2 hδp

theorem profile_right_eventually (N : Int) (c : Int → ℝ) (hc : IncreasingCuts N c)
    (j : Int) (hj : 0 ≤ j) (hjN : j < N) (f : ℝ → ℝ)
    (hf : Tendsto f (𝓝 0) (𝓝 (c j)))
    (hside : ∀ᶠ δ in 𝓝 (0:ℝ), 0 < δ → c j < f δ) :
    ∀ᶠ δ in 𝓝 (0:ℝ), 0 < δ → Profile N c (2*j+1) (f δ) := by
  have hgap : c j < c (j+1) := hc j (j+1) hj (by omega) (by omega)
  have hhi := Filter.Tendsto.eventually_lt_const hgap hf
  apply (hhi.and hside).mono
  intro δ hδ hδp
  right; right; right
  exact ⟨j,hj,hjN,rfl,hδ.2 hδp,hδ.1⟩

#print axioms profile_strict_order
#print axioms finite_order_persistence
end Kobon.BBLProfiles
