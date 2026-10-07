import Kobon.UpperOpenMathTripleDegreeThree

/-! Exact mixed-multiplicity discharging and equality classification for
shared core degree at most four, with a unit correction for full two-cap triples. This finite algebra is used only after
the geometric fans and their marked target incidences are extracted. -/
namespace Kobon.UpperOpenMathMixedDegreeFourWeights
open Finset
open scoped BigOperators
set_option maxHeartbeats 1000000

theorem finite_mixed_four_weight_rigidity {β : Type*} [DecidableEq β]
    (P : Finset β) (r a d : β → ℕ)
    (hr : ∀ p∈P, 3≤r p)
    (ha : ∀ p∈P, a p≤2*r p-3)
    (had : ∀ p∈P, a p+d p≤2*r p)
    (hd : ∀ p∈P, d p≤4)
    (hfive : ∀ p∈P, r p=3 → a p+d p≠5)
    (hext : ∀ p∈P, r p=3 → a p=3 → d p=3)
    (capacity : 3*(P.filter (fun p => r p=3 ∧ a p=3)).card≤
      (∑ p∈P.filter (fun p => r p=3 ∧ a p≤1 ∧ a p+d p≤2), d p)+
      ∑ p∈P.filter (fun p => 4≤r p), d p) :
    (0≤(∑ p∈P, (if 4≤r p then 4*(r p : ℤ)-2*a p-d p else
      2*(r p : ℤ)*(r p-2)-2*a p-d p))+2*(P.filter (fun p => r p=3 ∧ a p=2 ∧ d p=4)).card) ∧
    (((∑ p∈P, (if 4≤r p then 4*(r p : ℤ)-2*a p-d p else
      2*(r p : ℤ)*(r p-2)-2*a p-d p))+2*(P.filter (fun p => r p=3 ∧ a p=2 ∧ d p=4)).card)=0 →
      (P.filter (fun p => r p=3 ∧ a p≤1 ∧ a p+d p≤2))=∅ ∧
      (∑ p∈P.filter (fun p => 4≤r p), d p)=3*(P.filter (fun p => r p=3 ∧ a p=3)).card ∧
      (∀ p∈P, 4≤r p → a p+d p=2*r p) ∧
      (∀ p∈P, r p=3 → a p≠3 → a p=2 ∧ (d p=2 ∨ d p=4))) := by
  classical
  let E := P.filter (fun p => r p=3 ∧ a p=3)
  let B := P.filter (fun p => r p=3 ∧ a p≤1 ∧ a p+d p≤2)
  let H := P.filter (fun p => 4≤r p)
  let A := P.filter (fun p => r p=3 ∧ a p=2 ∧ d p=4)
  let W := fun p => if 4≤r p then 4*(r p : ℤ)-2*a p-d p else
    2*(r p : ℤ)*(r p-2)-2*a p-d p
  let R := fun p => W p+2*(if p∈A then 1 else 0)+3*(if p∈E then 1 else 0)-
    (if p∈B then (d p : ℤ)+2 else 0)-(if p∈H then d p else 0)
  have esub : E⊆P := filter_subset _ _
  have bsub : B⊆P := filter_subset _ _
  have hsub : H⊆P := filter_subset _ _
  have asub : A⊆P := filter_subset _ _
  have hpoint (p : β) (hp : p∈P) : 0≤R p := by
    have hpr := hr p hp
    have hpa := ha p hp
    have hpd := hd p hp
    have hpad := had p hp
    by_cases hh : p∈H
    · have hph := (mem_filter.mp hh).2
      have he : p∉E := by intro he; have hpe := (mem_filter.mp he).2.1; omega
      have hb : p∉B := by intro hb; have hpb := (mem_filter.mp hb).2.1; omega
      have hnA : p∉A := by intro hhA; have hhR := (mem_filter.mp hhA).2.1; omega
      simp only [R,W,hh,he,hb,hph,hnA,ite_true,ite_false]
      omega
    · have hpr3 : r p=3 := by
        have hnot : ¬4≤r p := fun h => hh (mem_filter.mpr ⟨hp,h⟩)
        omega
      have hpf := hfive p hp hpr3
      by_cases he : p∈E
      · have hpe := (mem_filter.mp he).2.2
        have hpde := hext p hp hpr3 hpe
        have hb : p∉B := by intro hb; have hpb := (mem_filter.mp hb).2.2.1; omega
        have hnA : p∉A := by intro hhA; have hhA2 := (mem_filter.mp hhA).2.2.1; omega
        simp [R,W,he,hb,hh,hnA,hpr3,hpe,hpde]
      · have hpea : a p≠3 := fun h => he (mem_filter.mpr ⟨hp,hpr3,h⟩)
        by_cases hb : p∈B
        · have hpb := (mem_filter.mp hb).2.2.2
          have hnA : p∉A := by intro hhA; have hhA2 := (mem_filter.mp hhA).2.2.1; have hpbA := (mem_filter.mp hb).2.2.1; omega
          simp only [R,W,he,hb,hh,hnA,ite_true,ite_false,hpr3]
          norm_num
          omega
        · by_cases hpA : p∈A
          · obtain ⟨_,_,haA,hdA⟩ := mem_filter.mp hpA
            simp [R,W,he,hb,hh,hpA,hpr3,haA,hdA]
          · have notA : ¬(a p=2 ∧ d p=4) := fun h => hpA (mem_filter.mpr ⟨hp,hpr3,h⟩)
            simp only [R,W,he,hb,hh,hpA,ite_true,ite_false,hpr3]
            norm_num
            omega
  have acount : (∑ p∈P, (if p∈A then (1 : ℤ) else 0))=A.card := by
    simp [inter_eq_right.mpr asub]
  have ecount : (∑ p∈P, (if p∈E then (1 : ℤ) else 0))=E.card := by
    simp [inter_eq_right.mpr esub]
  have bcount : (∑ p∈P, (if p∈B then (d p : ℤ)+2 else 0))=
      (∑ p∈B, (d p : ℤ))+2*B.card := by
    rw [← sum_filter,filter_mem_eq_inter,inter_eq_right.mpr bsub,sum_add_distrib]
    simp [mul_comm]
  have hcount : (∑ p∈P, (if p∈H then (d p : ℤ) else 0))=∑ p∈H, (d p : ℤ) := by
    rw [← sum_filter,filter_mem_eq_inter,inter_eq_right.mpr hsub]
  have residual : (∑ p∈P, R p)=(∑ p∈P, W p)+2*A.card+3*E.card-
      (∑ p∈B, (d p : ℤ))-2*B.card-(∑ p∈H, (d p : ℤ)) := by
    simp only [R,sum_sub_distrib,sum_add_distrib,← mul_sum,Nat.cast_ite,Nat.cast_zero]
    rw [acount,ecount,bcount,hcount]
    ring
  have capZ : 3*(E.card : ℤ)≤(∑ p∈B, (d p : ℤ))+∑ p∈H, (d p : ℤ) := by
    exact_mod_cast capacity
  have respos : 0≤∑ p∈P, R p := sum_nonneg hpoint
  have bpos : 0≤(B.card : ℤ) := by positivity
  constructor
  · change 0≤(∑ p∈P, W p)+2*A.card
    linarith
  · intro zero
    change (∑ p∈P, W p)+2*A.card=0 at zero
    have bz : B=∅ := card_eq_zero.mp (by omega)
    have hs := residual
    simp only [bz,sum_empty,card_empty,Nat.cast_zero,mul_zero,sub_zero] at hs
    have capEqZ : (∑ p∈H, (d p : ℤ))=3*(E.card : ℤ) := by
      simp only [bz,sum_empty,zero_add] at capZ
      linarith
    have rz : (∑ p∈P, R p)=0 := by linarith
    have each := (sum_eq_zero_iff_of_nonneg hpoint).mp rz
    refine ⟨bz,?_,?_,?_⟩
    · exact_mod_cast capEqZ
    · intro p hp hph
      have hh : p∈H := mem_filter.mpr ⟨hp,hph⟩
      have he : p∉E := by intro he; have hpe := (mem_filter.mp he).2.1; omega
      have hb : p∉B := by rw [bz]; exact notMem_empty p
      have eqp := each p hp
      simp only [R,W,he,hb,hh,hph,ite_true,ite_false] at eqp
      have hpd := hd p hp
      have hpa := ha p hp
      have hpad := had p hp
      omega
    · intro p hp hpr3 hpea
      have he : p∉E := fun h => hpea (mem_filter.mp h).2.2
      have hh : p∉H := by intro h; have hph := (mem_filter.mp h).2; omega
      have hb : p∉B := by rw [bz]; exact notMem_empty p
      have eqp := each p hp
      by_cases hpA : p∈A
      · obtain ⟨_,_,haA,hdA⟩ := mem_filter.mp hpA
        exact ⟨haA,Or.inr hdA⟩
      have notA : ¬(a p=2 ∧ d p=4) := fun h => hpA (mem_filter.mpr ⟨hp,hpr3,h⟩)
      simp only [R,W,he,hb,hh,hpA,ite_true,ite_false,hpr3] at eqp
      norm_num at eqp
      have hpa := ha p hp
      rw [hpr3] at hpa
      norm_num at hpa
      have hpd := hd p hp
      have hpf := hfive p hp hpr3
      omega

#print axioms finite_mixed_four_weight_rigidity
end Kobon.UpperOpenMathMixedDegreeFourWeights
