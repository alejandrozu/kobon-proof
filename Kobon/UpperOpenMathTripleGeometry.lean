import Kobon.UpperOpenMathRotation
import Mathlib.Tactic.FinCases

/-! Six genuine radial directions of a positively oriented triple fan give
six distinct noncentral outer points. No nearest-neighbor or whole-arrangement
fan-extraction premise is needed for this local geometric conclusion. -/
namespace Kobon.UpperOpenMathTripleGeometry
open Cells FanGeometry UpperFan Finset

theorem area_swap (c p q : Point) : areaDet c q p= -areaDet c p q := by
  dsimp [areaDet]
  ring

theorem area_antipodal_right (c p q : Point) (v : ℝ) :
    areaDet c p (c.1-v*(q.1-c.1),c.2-v*(q.2-c.2))=
      -v*areaDet c p q := by
  dsimp [areaDet]
  ring

theorem area_self (c p : Point) : areaDet c p p=0 := by
  dsimp [areaDet]
  ring

theorem point_ne_center {n : ℕ} {L : ℕ → Line ℝ}
    (f : UpperFan.Sectors n 3 L)
    (positive : ∀ z, 0<areaDet f.center (f.point z) (f.point (z+1)))
    (z : ZMod 6) : f.point z≠f.center := by
  intro h
  have hh := positive z
  rw [h] at hh
  simp [areaDet] at hh

theorem area_two_positive {n : ℕ} {L : ℕ → Line ℝ}
    (f : UpperFan.Sectors n 3 L)
    (positive : ∀ z, 0<areaDet f.center (f.point z) (f.point (z+1)))
    (z : ZMod 6) : 0<areaDet f.center (f.point z) (f.point (z+2)) := by
  obtain ⟨v,hv,he⟩ := f.antipodal z
  have he' : f.point (z+3)=
      (f.center.1-v*((f.point z).1-f.center.1),f.center.2-v*((f.point z).2-f.center.2)) := by
    simpa using he
  have hp := positive (z+2)
  have hi : z+2+1=z+3 := by ring
  rw [hi,he',area_antipodal_right,area_swap] at hp
  nlinarith

theorem antipodal_point_ne {n : ℕ} {L : ℕ → Line ℝ}
    (f : UpperFan.Sectors n 3 L)
    (positive : ∀ z, 0<areaDet f.center (f.point z) (f.point (z+1)))
    (z : ZMod 6) : f.point z≠f.point (z+3) := by
  intro hh
  obtain ⟨v,hv,he⟩ := f.antipodal z
  have he' : f.point (z+3)=
      (f.center.1-v*((f.point z).1-f.center.1),f.center.2-v*((f.point z).2-f.center.2)) := by
    simpa using he
  rw [← hh] at he'
  have h₁ := congrArg Prod.fst he'
  have h₂ := congrArg Prod.snd he'
  have hpos : 0<1+v := by linarith
  apply point_ne_center f positive z
  apply Prod.ext <;> dsimp at h₁ h₂ ⊢
  · have ht : (1+v)*((f.point z).1-f.center.1)=0 := by nlinarith
    have := (mul_eq_zero.mp ht).resolve_left hpos.ne'
    linarith
  · have ht : (1+v)*((f.point z).2-f.center.2)=0 := by nlinarith
    have := (mul_eq_zero.mp ht).resolve_left hpos.ne'
    linarith

theorem offset_point_ne {n : ℕ} {L : ℕ → Line ℝ}
    (f : UpperFan.Sectors n 3 L)
    (positive : ∀ z, 0<areaDet f.center (f.point z) (f.point (z+1)))
    (z : ZMod 6) (d : Fin 6) (hd : d.val≠0) :
    f.point z≠f.point (z+(d.val : ZMod 6)) := by
  fin_cases d
  · exact False.elim (hd rfl)
  · intro h
    have hh := positive z
    simp only [Nat.cast_one,h,area_self] at hh
    linarith
  · intro h
    have hh := area_two_positive f positive z
    simp only [Nat.cast_ofNat,h,area_self] at hh
    linarith
  · exact antipodal_point_ne f positive z
  · intro h
    have h' : f.point z=f.point (z+4) := by simpa using h
    obtain ⟨v,hv,he⟩ := f.antipodal (z+1)
    have he' : f.point (z+1+3)=
      (f.center.1-v*((f.point (z+1)).1-f.center.1),f.center.2-v*((f.point (z+1)).2-f.center.2)) := by
      simpa using he
    have hi : z+1+(3 : ZMod 6)=z+4 := by ring
    rw [hi] at he'
    have hz : areaDet f.center (f.point z) (f.point (z+4))=0 := by
      rw [← h',area_self]
    rw [he',area_antipodal_right] at hz
    have hp := positive z
    nlinarith [mul_pos hv hp]
  · intro h
    have h' : f.point z=f.point (z+5) := by simpa using h
    have hi : z+(5 : ZMod 6)+1=z := by
      have h6 : (5 : ZMod 6)+1=0 := by decide
      calc z+5+1=z+(5+1) := by ring
           _=z := by rw [h6,add_zero]
    have hh := positive (z+5)
    rw [hi,← h',area_self] at hh
    linarith

/-- The map to actual outer points is injective for every positively
oriented antipodal triple fan. Distinct ray indices cannot hide repeated
core endpoints. -/
theorem point_injective {n : ℕ} {L : ℕ → Line ℝ}
    (f : UpperFan.Sectors n 3 L)
    (positive : ∀ z, 0<areaDet f.center (f.point z) (f.point (z+1))) :
    Function.Injective f.point := by
  intro a b he
  by_contra hne
  let d : Fin 6 := ⟨(b-a).val,ZMod.val_lt _⟩
  have hcast : (d.val : ZMod 6)=b-a := by
    exact ZMod.natCast_zmod_val (b-a)
  have hd : d.val≠0 := by
    intro hz
    have hh : b-a=0 := by rw [← hcast,hz,Nat.cast_zero]
    exact hne (sub_eq_zero.mp hh).symm
  apply offset_point_ne f positive a d hd
  have hi : a+(d.val : ZMod 6)=b := by rw [hcast]; ring
  simpa only [hi] using he

/-- The three nonordinary shared directions at an extremal triple fan are
three distinct actual points, not merely three formal ray labels. -/
theorem extremal_core_endpoint_card {n : ℕ} {L : ℕ → Line ℝ}
    (f : UpperFan.Sectors n 3 L)
    (positive : ∀ z, 0<areaDet f.center (f.point z) (f.point (z+1)))
    (hext : 3≤f.ordinaryShared.card) :
    (f.coreShared.image f.point).card=3 := by
  classical
  rw [card_image_of_injective _ (point_injective f positive)]
  exact f.core_shared_card_eq_three_of_extremal (by decide) hext

#print axioms point_injective
#print axioms extremal_core_endpoint_card
end Kobon.UpperOpenMathTripleGeometry
