import Kobon.ShiftedFurediPalasti
import Kobon.FurediPalastiTwoCaps
import Kobon.AllN

/-! A parity-sensitive, unconditional all-order construction.  The infinite
baseline uses a shifted trigonometric arrangement and one- or two-cap
projective changes of chart.  The envelope also retains every saved finite
certificate.  No successor recurrence or BBL construction is assumed. -/
namespace Kobon.Universal

def baseline (n : ℕ) : ℕ :=
  if n<3 then 0 else if n=3 then 1 else n*(n-3)/3+1+n%2

theorem zero_simple_lower_bound (n : ℕ) : SimpleLowerBound n 0 := by
  exact ⟨ShiftedFurediPalasti.arrangement n,ShiftedFurediPalasti.noParallel n,
    ShiftedFurediPalasti.noConcurrent n,[],by simp,by simp,by simp⟩

theorem product_remainder (n : ℕ) (hn : 3≤n) (h : n%3≠0) :
    (n*(n-3))%3=1 := by
  have hs : (n-3)%3=n%3 := by omega
  rw [Nat.mul_mod,hs]
  have hr : n%3=1 ∨ n%3=2 := by omega
  rcases hr with hr | hr <;> simp [hr]

/-- The geometric construction, including simplicity, for every natural order. -/
theorem baseline_sound (n : ℕ) : SimpleLowerBound n (baseline n) := by
  by_cases hsmall : n<3
  · simpa [baseline,hsmall] using zero_simple_lower_bound n
  by_cases hthree : n=3
  · subst n
    simpa [baseline,ShiftedFurediPalasti.lower] using
      ShiftedFurediPalasti.simple_lower_bound 3 (by omega)
  have hn : 4≤n := by omega
  by_cases heven : n%2=0
  · simpa [baseline,hsmall,hthree,heven,ShiftedFurediPalasti.lower] using
      ShiftedFurediPalasti.simple_lower_bound n (by omega)
  have hodd : n%2=1 := by omega
  by_cases hdiv : n%3=0
  · have hnform : 6*((n-3)/6)+3=n := by omega
    have hk : 1≤(n-3)/6 := by omega
    have ht := FurediPalastiTwoCaps.two_cap_simple_lower_bound ((n-3)/6) hk
    rw [hnform] at ht
    apply ht.mono
    unfold baseline FurediPalasti.lower
    simp only [if_neg hsmall,if_neg hthree,hodd]
    omega
  · have hnform : 2*(n/2)+1=n := by omega
    have ht := FurediPalastiWrap.one_cap_simple_lower_bound (n/2) (by omega)
    rw [hnform] at ht
    apply ht.mono
    have hr := product_remainder n (by omega) hdiv
    unfold baseline FurediPalasti.lower
    simp only [if_neg hsmall,if_neg hthree,hodd]
    omega

theorem classical_baseline (n : ℕ) : LowerBound n (baseline n) :=
  (baseline_sound n).classical

theorem baseline_formula (n : ℕ) (hn : 4≤n) :
    baseline n=n*(n-3)/3+1+n%2 := by
  simp [baseline,show ¬ n<3 by omega,show n≠3 by omega]

theorem classical_baseline_le (n : ℕ) : AllN.baseline n≤baseline n := by
  by_cases hn : 4≤n
  · rw [baseline_formula n hn]
    unfold AllN.baseline
    omega
  · have he : n=0 ∨ n=1 ∨ n=2 ∨ n=3 := by omega
    rcases he with rfl | rfl | rfl | rfl <;> decide +kernel

/-- Exact improvement over the earlier all-order FP baseline. -/
theorem baseline_improvement (n : ℕ) (hn : 4≤n) :
    baseline n=AllN.baseline n+(if n%3=0 then 1+n%2 else n%2) := by
  rw [baseline_formula n hn]
  unfold AllN.baseline
  by_cases hdiv : n%3=0
  · have hr : (n*(n-3))%3=0 := by rw [Nat.mul_mod,hdiv]; simp
    rw [if_pos hdiv]
    omega
  · have hr := product_remainder n (by omega) hdiv
    rw [if_neg hdiv]
    omega

theorem strict_at_odd_orders (n : ℕ) (hn : 4≤n) (hodd : n%2=1) :
    AllN.baseline n<baseline n := by
  rw [baseline_improvement n hn]
  split <;> omega

/-- Arithmetic distance to Tamura's polynomial; no upper theorem is assumed or proved here. -/
theorem polynomial_gap_exact (n : ℕ) (hn : 4≤n) :
    n*(n-2)/3=baseline n+(n/3+(if n%3=2 then 1 else 0)-1-n%2) := by
  rw [baseline_formula n hn]
  have he : n*(n-2)=n*(n-3)+n := by
    have h2 : n-2+2=n := by omega
    have h3 : n-3+3=n := by omega
    nlinarith
  rw [he]
  have hs : (n-3)%3=n%3 := by omega
  have hr : n%3=0 ∨ n%3=1 ∨ n%3=2 := by omega
  rcases hr with hr | hr | hr
  · have hp : (n*(n-3))%3=0 := by rw [Nat.mul_mod,hr]; simp
    rw [if_neg (by omega)]
    omega
  · have hp : (n*(n-3))%3=1 := by rw [Nat.mul_mod,hs,hr]
    rw [if_neg (by omega)]
    omega
  · have hp : (n*(n-3))%3=1 := by rw [Nat.mul_mod,hs,hr]
    rw [if_pos hr]
    omega

/-- Strongest saved finite value or the proved infinite construction. -/
def bound (n : ℕ) : ℕ := max (baseline n) (AllN.bound n)

theorem baseline_le (n : ℕ) : baseline n≤bound n := le_max_left _ _
theorem previous_le (n : ℕ) : AllN.bound n≤bound n := le_max_right _ _

theorem all_n (n : ℕ) : LowerBound n (bound n) := by
  unfold bound
  rcases le_total (baseline n) (AllN.bound n) with h | h
  · rw [max_eq_right h]
    exact AllN.all_n n
  · rw [max_eq_left h]
    exact classical_baseline n

theorem dominates_49_target (n : ℕ) (hn : 49≤n) :
    (n-1)^2/4+191≤bound n :=
  le_trans (AllN.dominates_49_target n hn) (previous_le n)

/-- A strict improvement of the old FP baseline at every positive multiple of six. -/
theorem strict_even_multiples (k : ℕ) (hk : 1≤k) :
    AllN.baseline (6*k)+1=baseline (6*k) := by
  rw [baseline_formula (6*k) (by omega)]
  have hr : (6*k*(6*k-3))%3=0 := by
    rw [Nat.mul_mod]
    have hzero : (6*k)%3=0 := by omega
    simp [hzero]
  have he : (6*k)%2=0 := by omega
  unfold AllN.baseline
  rw [he]
  omega

/-- Two more triangles than the old FP baseline at odd multiples of three ≥9. -/
theorem strict_odd_multiples (k : ℕ) (hk : 1≤k) :
    AllN.baseline (6*k+3)+2=baseline (6*k+3) := by
  rw [baseline_formula (6*k+3) (by omega)]
  have hr : ((6*k+3)*(6*k+3-3))%3=0 := by
    rw [Nat.mul_mod]
    have hzero : (6*k+3)%3=0 := by omega
    simp [hzero]
  have he : (6*k+3)%2=1 := by omega
  unfold AllN.baseline
  rw [he]
  omega

#print axioms baseline_sound
#print axioms all_n
end Kobon.Universal
