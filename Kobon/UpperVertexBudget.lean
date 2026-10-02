import Kobon.Cells
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Finset.Prod
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-!
# Actual line-intersection multiplicity counts

The vertices are the image of all ordered pairs of distinct indexed real
lines under their intersection map. Finite fiber counting proves the usual
multiplicity identity from the actual geometry. It also counts the total
number of successive intervals on the lines as the sum of each line's vertex
count minus one. Identifying that count with a single global geometric edge
inventory is kept as a separate remaining extraction step.
-/
namespace Kobon.UpperVertexBudget
open Cells Finset
open scoped BigOperators

noncomputable def vertices (n : ℕ) (L : ℕ → Line ℝ) : Finset Point := by
  classical
  exact (univ : Finset (Fin n)).offDiag.image
    (fun ij => intersection (L ij.1) (L ij.2))

noncomputable def supports (n : ℕ) (L : ℕ → Line ℝ) (p : Point) : Finset (Fin n) := by
  classical
  exact univ.filter (fun i => affineEval (L i) p=0)

noncomputable def onLine (n : ℕ) (L : ℕ → Line ℝ) (i : Fin n) : Finset Point := by
  classical
  exact (vertices n L).filter (fun p => affineEval (L i) p=0)

theorem intersection_eq_iff (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L)
    (i j : Fin n) (hij : i≠j) (p : Point) :
    intersection (L i) (L j)=p ↔ affineEval (L i) p=0 ∧ affineEval (L j) p=0 := by
  have hn := noParallel_any n L hL i j i.isLt j.isLt (fun h => hij (Fin.ext h))
  constructor
  · intro he
    rw [← he]
    exact ⟨intersection_on_left _ _ hn,intersection_on_right _ _ hn⟩
  · rintro ⟨hp,hq⟩
    exact two_lines_two_points (L i) (L j) _ p hn
      (intersection_on_left _ _ hn) hp (intersection_on_right _ _ hn) hq

theorem intersection_fiber (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L)
    (p : Point) :
    (univ : Finset (Fin n)).offDiag.filter
      (fun ij => intersection (L ij.1) (L ij.2)=p)=(supports n L p).offDiag := by
  classical
  ext ij
  simp only [mem_filter,mem_offDiag,mem_univ,true_and,supports]
  constructor
  · rintro ⟨hne,he⟩
    have hh := (intersection_eq_iff n L hL ij.1 ij.2 hne p).mp he
    exact ⟨hh.1,hh.2,hne⟩
  · rintro ⟨hi,hj,hne⟩
    exact ⟨hne,(intersection_eq_iff n L hL ij.1 ij.2 hne p).mpr
      ⟨hi,hj⟩⟩

theorem support_card_at_least_two (n : ℕ) (L : ℕ → Line ℝ)
    (hL : NoParallel n L) {p : Point} (hp : p∈vertices n L) :
    2≤(supports n L p).card := by
  classical
  obtain ⟨ij,hij,he⟩ := mem_image.mp hp
  have hne := (mem_offDiag.mp hij).2.2
  have hh := (intersection_eq_iff n L hL ij.1 ij.2 hne p).mp he
  have hs : {ij.1,ij.2}⊆supports n L p := by
    intro i hi
    simp only [mem_insert,mem_singleton] at hi
    rcases hi with rfl|rfl
    · exact mem_filter.mpr ⟨mem_univ _,hh.1⟩
    · exact mem_filter.mpr ⟨mem_univ _,hh.2⟩
  have hc := card_le_card hs
  simpa [hne] using hc

/-- Exact pair-intersection multiplicity identity, obtained from fibers of
the actual intersection map. -/
theorem multiplicity_identity (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) :
    (n : ℤ)*(n-1)=∑ p∈vertices n L,
      (supports n L p).card*((supports n L p).card-1 : ℤ) := by
  classical
  have hc := card_eq_sum_card_image
    (fun ij : Fin n × Fin n => intersection (L ij.1) (L ij.2))
    (univ : Finset (Fin n)).offDiag
  rw [offDiag_card] at hc
  simp only [card_univ,Fintype.card_fin] at hc
  have hf : n*n-n=∑ p∈vertices n L,
      ((supports n L p).card*(supports n L p).card-(supports n L p).card) := by
    rw [hc]
    apply sum_congr rfl
    intro p _
    rw [intersection_fiber n L hL p,offDiag_card]
  have hn : n≤n*n := by nlinarith
  have hcast := congrArg (fun k : ℕ => (k : ℤ)) hf
  rw [Nat.cast_sub hn,Nat.cast_mul,Nat.cast_sum] at hcast
  have hterms : (∑ p∈vertices n L,
      (((supports n L p).card*(supports n L p).card-(supports n L p).card : ℕ) : ℤ))=
      ∑ p∈vertices n L, (supports n L p).card*((supports n L p).card-1 : ℤ) := by
    apply sum_congr rfl
    intro p hp
    have hr := support_card_at_least_two n L hL hp
    rw [Nat.cast_sub (by nlinarith : (supports n L p).card≤
      (supports n L p).card*(supports n L p).card),Nat.cast_mul]
    ring
  rw [hterms] at hcast
  nlinarith

/-- Count real point-line incidences in either order. -/
theorem point_line_incidence (n : ℕ) (L : ℕ → Line ℝ) :
    (∑ i : Fin n, (onLine n L i).card)=
      ∑ p∈vertices n L, (supports n L p).card := by
  classical
  simp only [onLine,supports,card_eq_sum_ones,sum_filter]
  exact sum_comm

theorem onLine_nonempty (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L)
    (hn : 2≤n) (i : Fin n) : (onLine n L i).Nonempty := by
  classical
  have hex : ∃ j : Fin n, i≠j := by
    by_cases hi : i.val=0
    · exact ⟨⟨1,by omega⟩,by intro h; have he := congrArg Fin.val h; simp at he; omega⟩
    · exact ⟨⟨0,by omega⟩,by intro h; have he := congrArg Fin.val h; simp at he; omega⟩
  obtain ⟨j,hij⟩ := hex
  have hd := noParallel_any n L hL i j i.isLt j.isLt (fun h => hij (Fin.ext h))
  refine ⟨intersection (L i) (L j),mem_filter.mpr ⟨?_,intersection_on_left _ _ hd⟩⟩
  exact mem_image.mpr ⟨(i,j),mem_offDiag.mpr ⟨mem_univ _,mem_univ _,hij⟩,rfl⟩

/-- The total count of successive intervals on all supporting lines. The
right side uses actual intersection multiplicities, including ordinary
vertices whose contribution r(r-2) is zero. -/
theorem line_interval_budget (n : ℕ) (L : ℕ → Line ℝ)
    (hL : NoParallel n L) (hn : 2≤n) :
    (∑ i : Fin n, (((onLine n L i).card-1 : ℕ) : ℤ))=
      (n : ℤ)*(n-2)-∑ p∈vertices n L,
        (supports n L p).card*((supports n L p).card-2 : ℤ) := by
  classical
  have hline (i : Fin n) : (((onLine n L i).card-1 : ℕ) : ℤ)=
      ((onLine n L i).card : ℤ)-1 := by
    rw [Nat.cast_sub (by have := card_pos.mpr (onLine_nonempty n L hL hn i); omega)]
    norm_num
  simp_rw [hline]
  rw [sum_sub_distrib]
  simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one]
  have hpoint := congrArg (fun k : ℕ => (k : ℤ)) (point_line_incidence n L)
  simp only [Nat.cast_sum] at hpoint
  rw [hpoint]
  have hm := multiplicity_identity n L hL
  have hs : (∑ p∈vertices n L, (supports n L p).card*((supports n L p).card-1 : ℤ))=
      (∑ p∈vertices n L, (supports n L p).card*((supports n L p).card-2 : ℤ))+
      ∑ p∈vertices n L, ((supports n L p).card : ℤ) := by
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro p _
    ring
  rw [hs] at hm
  nlinarith

#print axioms multiplicity_identity
#print axioms point_line_incidence
#print axioms line_interval_budget
end Kobon.UpperVertexBudget


