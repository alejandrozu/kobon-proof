import Kobon.BBLTangentBounds
import Mathlib.Analysis.SpecialFunctions.Complex.Arctan
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.Positivity

/-!
# Rational certificates for arbitrary positive tangent-grid angles

Alternating finite arctangent sums bound the actual real arctangent.  A
certificate brackets a quarter angle, whose tangent is below tan(pi/8),
and doubles twice.  The analytic soundness proof uses only standard axioms;
the finite rational inequalities may be discharged by ordinary kernel
computation.  There is no assumed transcendental evaluation oracle.
-/

namespace Kobon.BBLRationalTangentBounds
open Real Finset Filter
open scoped Topology
set_option maxHeartbeats 0

noncomputable def atanPoly (terms : ℕ) (x : ℝ) : ℝ :=
  ∑ i∈range terms, (-1)^i*x^(2*i+1)/(2*i+1)

def atanPolyRat (terms : ℕ) (x : ℚ) : ℚ :=
  ∑ i∈range terms, (-1)^i*x^(2*i+1)/(2*i+1)

theorem coe_atanPolyRat (terms : ℕ) (x : ℚ) :
    (atanPolyRat terms x : ℝ)=atanPoly terms x := by
  simp only [atanPolyRat,atanPoly]
  push_cast
  rfl

theorem atanPoly_bounds {x : ℝ} (hx : 0≤x) (hu : x<1) (k : ℕ) :
    atanPoly (2*k) x≤arctan x ∧ arctan x≤atanPoly (2*k+1) x := by
  let f : ℕ→ℝ := fun i => x^(2*i+1)/(2*i+1)
  have hf : Antitone f := by
    refine antitone_nat_of_succ_le fun i => ?_
    have hpow : x^(2*(i+1)+1)≤x^(2*i+1) := by
      have he : 2*(i+1)+1=(2*i+1)+2 := by omega
      rw [he,pow_add]
      have hs : x^2≤1 := by nlinarith
      exact mul_le_of_le_one_right (pow_nonneg hx _) hs
    dsimp [f]
    apply div_le_div₀ (pow_nonneg hx _) hpow (by positivity)
    exact_mod_cast (show 2*i+1≤2*(i+1)+1 by omega)
  have hnorm : ‖x‖<1 := by simpa only [Real.norm_eq_abs,abs_of_nonneg hx] using hu
  have hs := Real.hasSum_arctan hnorm
  have ht : Tendsto (fun n => ∑ i∈range n,(-1:ℝ)^i*f i)
      atTop (𝓝 (arctan x)) := by
    simpa only [f,mul_div_assoc,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one]
      using hs.tendsto_sum_nat
  constructor
  · simpa only [atanPoly,f,mul_div_assoc] using hf.alternating_series_le_tendsto ht k
  · simpa only [atanPoly,f,mul_div_assoc] using hf.tendsto_le_alternating_series ht k

noncomputable def twice (x : ℝ) : ℝ := 2*x/(1-x^2)
def twiceRat (x : ℚ) : ℚ := 2*x/(1-x^2)

theorem coe_twiceRat (x : ℚ) : (twiceRat x : ℝ)=twice x := by
  simp only [twiceRat,twice]
  push_cast
  rfl

theorem twice_nonneg {x : ℝ} (hx : 0≤x) (hu : x<1) : 0≤twice x := by
  unfold twice
  apply div_nonneg (by positivity)
  nlinarith

theorem twice_mono {x y : ℝ} (hx : 0≤x) (hxy : x≤y) (hy : y<1) :
    twice x≤twice y := by
  have hy0 : 0≤y := le_trans hx hxy
  unfold twice
  apply div_le_div₀ (by positivity) (by linarith) (by nlinarith)
  nlinarith

theorem twice_tan (x : ℝ) : tan (2*x)=twice (tan x) := by
  rw [tan_two_mul]
  rfl

theorem tangent_lower_of_arctan {x θ : ℝ}
    (hlo : -(π/2)<θ) (hhi : θ<π/2) (h : arctan x≤θ) : x≤tan θ := by
  have hm := strictMonoOn_tan.monotoneOn
    ⟨neg_pi_div_two_lt_arctan x,arctan_lt_pi_div_two x⟩ ⟨hlo,hhi⟩ h
  simpa only [tan_arctan] using hm

theorem tangent_upper_of_arctan {x θ : ℝ}
    (hlo : -(π/2)<θ) (hhi : θ<π/2) (h : θ≤arctan x) : tan θ≤x := by
  have hm := strictMonoOn_tan.monotoneOn ⟨hlo,hhi⟩
    ⟨neg_pi_div_two_lt_arctan x,arctan_lt_pi_div_two x⟩ h
  simpa only [tan_arctan] using hm

/-- The precision is a certificate parameter, not a hypothesis about a
floating approximation. -/
theorem quarter_atan_sound (θ lo hi : ℝ) (terms : ℕ)
    (hθ : 0<θ) (hθu : θ<π/2)
    (hlo : 0≤lo) (hlou : lo<1) (hhi : 0≤hi) (hhiu : hi<1)
    (htwice : twice hi<1)
    (hL : atanPoly (2*terms+1) lo≤θ/4)
    (hU : θ/4≤atanPoly (2*terms) hi) :
    twice (twice lo)≤tan θ ∧ tan θ≤twice (twice hi) := by
  obtain ⟨_,hAL⟩ := atanPoly_bounds hlo hlou terms
  obtain ⟨hAU,_⟩ := atanPoly_bounds hhi hhiu terms
  have low : lo≤tan (θ/4) := tangent_lower_of_arctan
    (by linarith [pi_pos]) (by linarith) (le_trans hAL hL)
  have high : tan (θ/4)≤hi := tangent_upper_of_arctan
    (by linarith [pi_pos]) (by linarith) (le_trans hU hAU)
  obtain ⟨hp,hu⟩ := BBLTangentBounds.tan_small (θ/4)
    (by linarith) (by linarith)
  have first : twice lo≤tan (θ/2) ∧ tan (θ/2)≤twice hi := by
    have he : 2*(θ/4)=θ/2 := by ring
    rw [←he,twice_tan]
    exact ⟨twice_mono hlo low hu,twice_mono hp.le high hhiu⟩
  obtain ⟨hp2,hu2⟩ := BBLTangentBounds.tan_small (θ/2)
    (by linarith) (by linarith)
  have he : 2*(θ/2)=θ := by ring
  rw [←he,twice_tan]
  exact ⟨twice_mono (twice_nonneg hlo hlou) first.1 hu2,
    twice_mono hp2.le first.2 htwice⟩

def piLower : ℚ := 314159265358979323846/100000000000000000000
def piUpper : ℚ := 314159265358979323847/100000000000000000000

theorem pi_bounds : (piLower : ℝ)≤π ∧ π≤(piUpper : ℝ) := by
  constructor
  · convert Real.pi_gt_d20.le using 1 <;> first | rfl | norm_num [piLower]
  · convert Real.pi_lt_d20.le using 1 <;> first | rfl | norm_num [piUpper]

noncomputable def angle (n k : ℕ) : ℝ := (k:ℝ)*π/(n:ℝ)

theorem angle_positive {n k : ℕ} (hn : 0<n) (hk : 0<k) : 0<angle n k := by
  unfold angle
  positivity

theorem angle_lt_half {n k : ℕ} (hn : 0<n) (hk : 2*k<n) : angle n k<π/2 := by
  have hnR : (0:ℝ)<n := by exact_mod_cast hn
  have hkR : 2*(k:ℝ)<n := by exact_mod_cast hk
  unfold angle
  apply (div_lt_iff₀ hnR).mpr
  nlinarith [pi_pos]

theorem angle_quarter_bounds {n k : ℕ} (hn : 0<n) :
    (k:ℝ)*(piLower:ℝ)/(4*(n:ℝ))≤angle n k/4 ∧
    angle n k/4≤(k:ℝ)*(piUpper:ℝ)/(4*(n:ℝ)) := by
  have hnR : (0:ℝ)<n := by exact_mod_cast hn
  have hkR : (0:ℝ)≤k := by positivity
  obtain ⟨hl,hu⟩ := pi_bounds
  have he : angle n k/4=(k:ℝ)*π/(4*(n:ℝ)) := by
    unfold angle
    ring
  rw [he]
  constructor
  · exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hl hkR) (by positivity)
  · exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hu hkR) (by positivity)

/-- Every condition is a finite rational computation. -/
def QuarterCheck (n k terms : ℕ) (lo hi : ℚ) : Prop :=
  0<n ∧ 0<k ∧ 2*k<n ∧
  0≤lo ∧ lo<1 ∧ 0≤hi ∧ hi<1 ∧ twiceRat hi<1 ∧
  atanPolyRat (2*terms+1) lo≤(k:ℚ)*piLower/(4*(n:ℚ)) ∧
  (k:ℚ)*piUpper/(4*(n:ℚ))≤atanPolyRat (2*terms) hi

instance (n k terms : ℕ) (lo hi : ℚ) : Decidable (QuarterCheck n k terms lo hi) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

theorem quarterCheck_sound {n k terms : ℕ} {lo hi : ℚ}
    (h : QuarterCheck n k terms lo hi) :
    (twiceRat (twiceRat lo) : ℝ)≤tan (angle n k) ∧
    tan (angle n k)≤(twiceRat (twiceRat hi) : ℝ) := by
  obtain ⟨hn,hk,hkn,hl0,hl1,hh0,hh1,htw,hL,hU⟩ := h
  have hl0R : (0:ℝ)≤(lo:ℝ) := by exact_mod_cast hl0
  have hl1R : (lo:ℝ)<1 := by exact_mod_cast hl1
  have hh0R : (0:ℝ)≤(hi:ℝ) := by exact_mod_cast hh0
  have hh1R : (hi:ℝ)<1 := by exact_mod_cast hh1
  have htwR : twice (hi:ℝ)<1 := by
    rw [←coe_twiceRat]
    exact_mod_cast htw
  obtain ⟨hπL,hπU⟩ := angle_quarter_bounds (k:=k) hn
  have hLR : atanPoly (2*terms+1) (lo:ℝ)≤angle n k/4 := by
    have hh : (atanPolyRat (2*terms+1) lo : ℝ)≤
        (k:ℝ)*(piLower:ℝ)/(4*(n:ℝ)) := by exact_mod_cast hL
    rw [coe_atanPolyRat] at hh
    exact le_trans hh hπL
  have hUR : angle n k/4≤atanPoly (2*terms) (hi:ℝ) := by
    have hh : (k:ℝ)*(piUpper:ℝ)/(4*(n:ℝ))≤
        (atanPolyRat (2*terms) hi : ℝ) := by exact_mod_cast hU
    rw [coe_atanPolyRat] at hh
    exact le_trans hπU hh
  have hs := quarter_atan_sound (angle n k) (lo:ℝ) (hi:ℝ) terms
    (angle_positive hn hk) (angle_lt_half hn hkn)
    hl0R hl1R hh0R hh1R htwR hLR hUR
  simpa only [coe_twiceRat] using hs

#print axioms atanPoly_bounds
#print axioms quarter_atan_sound
#print axioms quarterCheck_sound
end Kobon.BBLRationalTangentBounds
