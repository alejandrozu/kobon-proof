import Kobon.UpperOpenMathMarkedCurvatureWeights

/-! A conditional sharper finite weighted discharging rule using the actual number of unmarked
full-two-cap neighbors at each nonfull target. Geometry and cross-edge
counting must supply the displayed capacity and cone hypotheses. The residual J counts precisely the one-cap degree-three targets meeting
three unmarked full two-cap sources. No geometric exclusion of J is assumed. -/
namespace Kobon.UpperOpenMathRefinedHalfCurvatureWeights
open Finset UpperOpenMathMarkedCurvatureWeights
open scoped BigOperators
set_option maxHeartbeats 1000000

theorem finite_refined_half_curvature {β : Type*} [DecidableEq β]
    (P : Finset β) (a d m x : β → ℕ)
    (ha : ∀ p∈P, a p≤3) (had : ∀ p∈P, a p+d p≤6)
    (hfive : ∀ p∈P, a p+d p≠5)
    (hext : ∀ p∈P, a p=3 → d p=3 ∧ m p=3)
    (hx : ∀ p∈P, x p≤d p)
    (hfull : ∀ p∈P, a p+d p=6 → x p=0)
    (hbalanced : ∀ p∈P, a p=2 → d p=2 → m p=0 → x p=0)
    (capacity : (∑ p∈P,m p)+(∑ p∈P.filter (fun p => a p≤1 ∧ a p+d p≤2),x p)≤
      ∑ p∈P.filter (fun p => a p≤1 ∧ a p+d p≤2),d p)
    (cone : 2*(P.filter (fun p => a p=2 ∧ d p=4 ∧ m p=0)).card≤∑ p∈P,x p) :
    0≤2*(∑ p∈P,(6-2*(a p : ℤ)-d p))+
      2*((P.filter (fun p => a p=2 ∧ d p=4 ∧ m p=0)).card : ℤ)+
      2*((P.filter (fun p => a p=1 ∧ d p=5)).card : ℤ)+
      ((P.filter (fun p => a p=1 ∧ d p=3 ∧ x p=3)).card : ℤ) := by
  classical
  let B := P.filter (fun p => a p≤1 ∧ a p+d p≤2)
  let A := P.filter (fun p => a p=2 ∧ d p=4 ∧ m p=0)
  let F := P.filter (fun p => a p=1 ∧ d p=5)
  let J := P.filter (fun p => a p=1 ∧ d p=3 ∧ x p=3)
  let W := fun p => 6-2*(a p : ℤ)-d p
  let Q := fun p => W p+unpaidWeight (a p) (d p) (m p)+2*m p-
    (if p∈B then 2*(d p : ℤ) else 0)
  have point (p : β) (hp : p∈P) :
      (x p : ℤ)≤2*Q p+(if p∈B then 4*(x p : ℤ) else 0)+
        (if p∈J then 1 else 0) := by
    have hap := ha p hp
    have hadp := had p hp
    have hfp := hfive p hp
    have hxp := hx p hp
    have hnp : p∉J → a p=1 → d p=3 → x p≤2 := by
      intro hnj hap hdp
      have hnjp : ¬(a p=1 ∧ d p=3 ∧ x p=3) :=
        fun hh => hnj (mem_filter.mpr ⟨hp,hh⟩)
      omega
    by_cases ha3 : a p=3
    · obtain ⟨hd3,hm3⟩ := hext p hp ha3
      have hx0 := hfull p hp (by omega)
      have hb : p∉B := by intro hh; have hh' := (mem_filter.mp hh).2.1; omega
      dsimp [Q,W]
      rw [hx0,ha3,hd3,hm3]
      simp only [hb,unpaidWeight]
      split_ifs <;> norm_num <;> omega
    · by_cases hb : p∈B
      · obtain ⟨hal,hsum⟩ := (mem_filter.mp hb).2
        dsimp [Q,W]
        simp only [if_pos hb]
        unfold unpaidWeight
        split_ifs <;> omega
      · have hnot : ¬(a p≤1 ∧ a p+d p≤2) := fun hh => hb (mem_filter.mpr ⟨hp,hh⟩)
        by_cases full : a p+d p=6
        · have hx0 := hfull p hp full
          dsimp [Q,W]
          simp only [if_neg hb]
          rw [hx0]
          unfold unpaidWeight
          split_ifs <;> omega
        · by_cases balanced : a p=2 ∧ d p=2 ∧ m p=0
          · have hx0 := hbalanced p hp balanced.1 balanced.2.1 balanced.2.2
            dsimp [Q,W]
            simp only [if_neg hb]
            rw [hx0]
            unfold unpaidWeight
            split_ifs <;> omega
          · by_cases n13 : a p=1 ∧ d p=3
            · have narrow : (x p : ℤ)≤2+(if p∈J then 1 else 0) := by
                split_ifs with hj
                · omega
                · have h := hnp hj n13.1 n13.2
                  omega
              dsimp [Q,W]
              simp only [if_neg hb]
              unfold unpaidWeight
              split_ifs at narrow ⊢ <;> omega
            · dsimp [Q,W]
              simp only [if_neg hb]
              unfold unpaidWeight
              split_ifs <;> omega
  have total := sum_le_sum point
  have bsub : B⊆P := filter_subset _ _
  have dsum : (∑ p∈P, if p∈B then 2*(d p : ℤ) else 0)=2*∑ p∈B,(d p : ℤ) := by
    rw [← sum_filter,filter_mem_eq_inter,inter_eq_right.mpr bsub,mul_sum]
  have xsum : (∑ p∈P, if p∈B then 4*(x p : ℤ) else 0)=4*∑ p∈B,(x p : ℤ) := by
    rw [← sum_filter,filter_mem_eq_inter,inter_eq_right.mpr bsub,mul_sum]
  have eachUnpaid (p : β) (hp : p∈P) : unpaidWeight (a p) (d p) (m p)=
      2*(if p∈A then (1 : ℤ) else 0)+(if p∈F then (1 : ℤ) else 0) := by
    by_cases hA : a p=2 ∧ d p=4 ∧ m p=0
    · have hF : ¬(a p=1 ∧ d p=5) := by omega
      simp [unpaidWeight,A,F,hp,hA,hF]
    · simp [unpaidWeight,A,F,hp,hA]
  have unpaidSum : (∑ p∈P,unpaidWeight (a p) (d p) (m p))=2*(A.card : ℤ)+F.card := by
    rw [sum_congr rfl eachUnpaid,sum_add_distrib,← mul_sum]
    have asub : A⊆P := filter_subset _ _
    have fsub : F⊆P := filter_subset _ _
    simp [inter_eq_right.mpr asub, inter_eq_right.mpr fsub]
  have qsum : (∑ p∈P,Q p)=(∑ p∈P,W p)+2*A.card+F.card+
      2*(∑ p∈P,(m p : ℤ))-2*(∑ p∈B,(d p : ℤ)) := by
    change (∑ p∈P,(W p+unpaidWeight (a p) (d p) (m p)+2*m p-
      (if p∈B then 2*(d p : ℤ) else 0)))=_
    rw [sum_sub_distrib,sum_add_distrib,sum_add_distrib,unpaidSum,dsum,← mul_sum]
    ring
  have jsum : (∑ p∈P, if p∈J then (1 : ℤ) else 0)=J.card := by
    have jsub : J⊆P := filter_subset _ _
    simp [inter_eq_right.mpr jsub]
  have capZ : (∑ p∈P,(m p : ℤ))+(∑ p∈B,(x p : ℤ))≤∑ p∈B,(d p : ℤ) := by
    exact_mod_cast capacity
  have coneZ : 2*(A.card : ℤ)≤∑ p∈P,(x p : ℤ) := by exact_mod_cast cone
  simp only [sum_add_distrib,← mul_sum] at total
  rw [xsum,qsum,jsum] at total
  change 0≤2*(∑ p∈P,W p)+2*A.card+2*F.card+J.card
  linarith

#print axioms finite_refined_half_curvature
end Kobon.UpperOpenMathRefinedHalfCurvatureWeights
