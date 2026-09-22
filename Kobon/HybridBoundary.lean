import Kobon.Exterior
import Kobon.SeedFamily
import Mathlib.Tactic.Positivity

/-! Geometric and parametric boundary certificates for the hybrid construction.

This module does not assume a future triangle count.  A rational box certificate
proves the signs defining an actual visible pair, and the existing exterior
construction then produces real lines and triangles.
-/
namespace Kobon.HybridBoundary
open Exterior Parametric

theorem det_skew (l m : Line ℝ) : det l m = -det m l := by
  dsimp [det]
  ring

theorem derivative_nonneg_iff (r l w : Line ℝ) (h : det w l ≠ 0) :
    0 ≤ derivative r l w ↔ 0 ≤ det r l * det w l := by
  dsimp [derivative]
  constructor
  · intro hh
    have hsq : 0 ≤ (det w l)^2 := sq_nonneg _
    have hh' := mul_nonneg hh hsq
    field_simp at hh'
    nlinarith
  · intro hh
    have heq : det r l / det w l = (det r l * det w l)/(det w l)^2 := by
      field_simp
    rw [heq]
    exact div_nonneg hh (sq_nonneg _)

theorem derivative_nonpos_iff (r l w : Line ℝ) (h : det w l ≠ 0) :
    derivative r l w ≤ 0 ↔ det r l * det w l ≤ 0 := by
  dsimp [derivative]
  have heq : det r l / det w l = (det r l * det w l)/(det w l)^2 := by
    field_simp
  rw [heq]
  rw [div_le_iff₀ (sq_pos_of_ne_zero h),zero_mul]

def normalLine (a b : ℚ) : Line ℝ := ⟨a,b,0⟩

def derivativeNumerator {d : Nat} (r l : ParamLine d) (a b : ℚ) : ℚ :=
  determinant r l * (a*l.b-b*l.a)

def VisibleCheck {d : Nat} (n : Nat) (lo hi : Form d)
    (L : Nat → ParamLine d) (a b : ℚ) (t : Triple) : Prop :=
  t.i<t.j ∧ t.j<n ∧ t.k=n ∧ ∀ r : Fin n,
    (0 ≤ lower lo hi (orientedForm (L r) (L t.i) (L t.j)) ∧
     0 ≤ derivativeNumerator (L r) (L t.i) a b ∧
     0 ≤ derivativeNumerator (L r) (L t.j) a b) ∨
    (upper lo hi (orientedForm (L r) (L t.i) (L t.j)) ≤ 0 ∧
     derivativeNumerator (L r) (L t.i) a b ≤ 0 ∧
     derivativeNumerator (L r) (L t.j) a b ≤ 0)

instance {d : Nat} (n : Nat) (lo hi : Form d) (L : Nat → ParamLine d)
    (a b : ℚ) (t : Triple) : Decidable (VisibleCheck n lo hi L a b t) := by
  unfold VisibleCheck
  infer_instance

def AdmissibleCheck {d : Nat} (n : Nat) (L : Nat → ParamLine d) (a b : ℚ) : Prop :=
  ∀ i : Fin n, (L i).a*b-(L i).b*a ≠ 0

instance {d : Nat} (n : Nat) (L : Nat → ParamLine d) (a b : ℚ) :
    Decidable (AdmissibleCheck n L a b) := by
  unfold AdmissibleCheck
  infer_instance

theorem admissible_sound {d : Nat} (n : Nat) (L : Nat → ParamLine d)
    (a b : ℚ) (x : Fin d → ℝ) (hc : AdmissibleCheck n L a b) :
    Admissible n (fun i => toLine (L i) x) (normalLine a b) := by
  intro i
  have hh := hc i
  dsimp [det,toLine,normalLine]
  exact_mod_cast hh

theorem visible_sound {d : Nat} (n : Nat) (lo hi : Form d)
    (L : Nat → ParamLine d) (a b : ℚ) (x : Fin d → ℝ)
    (hx : InBox lo hi x) (hp : DirectionCheck n L)
    (hw : AdmissibleCheck n L a b) (t : Triple)
    (hc : VisibleCheck n lo hi L a b t) :
    VisiblePair n (fun i => toLine (L i) x) (normalLine a b) t := by
  rcases hc with ⟨hij,hjn,hkn,hc⟩
  have hin : t.i<n := by omega
  have hp' := directions_sound n L x hp
  have hw' := admissible_sound n L a b x hw
  have hd := hp' ⟨t.i,hin⟩ ⟨t.j,hjn⟩ hij
  have hwi : det (normalLine a b) (toLine (L t.i) x) ≠ 0 := by
    rw [det_skew]
    exact neg_ne_zero.mpr (hw' ⟨t.i,hin⟩)
  have hwj : det (normalLine a b) (toLine (L t.j) x) ≠ 0 := by
    rw [det_skew]
    exact neg_ne_zero.mpr (hw' ⟨t.j,hjn⟩)
  refine ⟨hij,hjn,hkn,?_⟩
  intro r
  have numerator (i : Nat) :
      (derivativeNumerator (L r) (L i) a b : ℝ) =
        det (toLine (L r) x) (toLine (L i) x) *
          det (normalLine a b) (toLine (L i) x) := by
    simp [derivativeNumerator,determinant,det,toLine,normalLine]
  rcases hc r with ⟨he,hdi,hdj⟩ | ⟨he,hdi,hdj⟩
  · left
    refine ⟨?_,?_,?_⟩
    · apply (oriented_nonneg_iff _ _ _ hd).mp
      rw [← orientedForm_value]
      exact nonneg_of_lower lo hi _ x hx he
    · apply (derivative_nonneg_iff _ _ _ hwi).mpr
      rw [← numerator t.i]
      exact_mod_cast hdi
    · apply (derivative_nonneg_iff _ _ _ hwj).mpr
      rw [← numerator t.j]
      exact_mod_cast hdj
  · right
    refine ⟨?_,?_,?_⟩
    · apply (oriented_nonpos_iff _ _ _ hd).mp
      rw [← orientedForm_value]
      exact nonpos_of_upper lo hi _ x hx he
    · apply (derivative_nonpos_iff _ _ _ hwi).mpr
      rw [← numerator t.i]
      exact_mod_cast hdi
    · apply (derivative_nonpos_iff _ _ _ hwj).mpr
      rw [← numerator t.j]
      exact_mod_cast hdj

def seedPairs : List Triple := [⟨0,10,11⟩,⟨1,3,11⟩,⟨2,4,11⟩,⟨5,7,11⟩,⟨6,8,11⟩]

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem seed_admissible_check : AdmissibleCheck 11 SeedFamily.lineAt 10 (-13) := by
  decide +kernel

theorem seed_visible_checks :
    seedPairs.all (fun t => decide
      (VisibleCheck 11 SeedFamily.lo SeedFamily.hi SeedFamily.lineAt 10 (-13) t)) = true := by
  decide +kernel

theorem seed_visible (epsilon : ℝ) (he : 0<epsilon) (hu : epsilon≤1/100000)
    (t : Triple) (ht : t ∈ seedPairs) :
    VisiblePair 11 (SeedFamily.arrangement epsilon) (normalLine 10 (-13)) t := by
  have hc := seed_visible_checks
  simp only [List.all_eq_true,decide_eq_true_eq] at hc
  exact visible_sound 11 SeedFamily.lo SeedFamily.hi SeedFamily.lineAt 10 (-13)
    (SeedFamily.parameters epsilon) (SeedFamily.parameters_in_box epsilon he hu)
    SeedFamily.directions seed_admissible_check t (hc t ht)

/-- Every certified real trigonometric seed admits a five-triangle exterior gain. -/
theorem seed_exterior (epsilon : ℝ) (he : 0<epsilon) (hu : epsilon≤1/100000) :
    SimpleLowerBound 12 37 := by
  let L := SeedFamily.arrangement epsilon
  let w := normalLine 10 (-13)
  have hp := SeedFamily.no_parallel epsilon
  have hs := SeedFamily.no_concurrent epsilon he hu
  have hnt := increasing_nodup 11 SeedFamily.triangles SeedFamily.ordered
  have hw : Admissible 11 L w :=
    admissible_sound 11 SeedFamily.lineAt 10 (-13) (SeedFamily.parameters epsilon)
      seed_admissible_check
  have hnn : seedPairs.Nodup := by decide +kernel
  have h := Exterior.extension 11 32 L SeedFamily.triangles seedPairs w
    (safeHeight 11 L w) hp hs hnt (SeedFamily.all_triangles epsilon he hu)
    (by decide) hnn (seed_visible epsilon he hu) hw (safeHeight_beyond 11 L w)
  simpa [seedPairs] using h

#print axioms seed_exterior
end Kobon.HybridBoundary
