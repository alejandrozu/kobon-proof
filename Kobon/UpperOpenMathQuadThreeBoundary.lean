import Kobon.UpperOpenMathCevianCrossing

/-! Any three outer corners of a strict antipodal star bound its center. -/
namespace Kobon.UpperOpenMathQuadThreeBoundary
open Cells UpperOpenMathAntipodalCenterUniqueness UpperOpenMathCevianCrossing
set_option maxHeartbeats 1000000

theorem area_between_zero (p q c : Point) (bet : Between c p q) : areaDet p q c=0 := by
  obtain ⟨u,v,hu,hv,he⟩ := between_area p q c p q bet
  have pp : areaDet p q p=0 := by unfold areaDet; ring
  have qq : areaDet p q q=0 := by unfold areaDet; ring
  rw [pp,qq] at he
  simpa using he

theorem four_corner_areas_positive (c p q r s : Point) (pos : 0<areaDet c p q)
    (pr : Between c p r) (qs : Between c q s) :
    0<areaDet p q r ∧ 0<areaDet p q s ∧ 0<areaDet p r s ∧ 0<areaDet q r s := by
  have pqc : areaDet p q c=areaDet c p q := by unfold areaDet; ring
  have pqP : areaDet p q p=0 := by unfold areaDet; ring
  have pqQ : areaDet p q q=0 := by unfold areaDet; ring
  have pqr : 0<areaDet p q r := by
    obtain ⟨u,v,hu,hv,he⟩ := between_area p q c p r pr
    rw [pqc,pqP] at he
    by_contra h
    have le : areaDet p q r≤0 := le_of_not_gt h
    have nonpos := mul_nonpos_of_nonneg_of_nonpos hv.le le
    linarith
  have pqs : 0<areaDet p q s := by
    obtain ⟨u,v,hu,hv,he⟩ := between_area p q c q s qs
    rw [pqc,pqQ] at he
    by_contra h
    have le : areaDet p q s≤0 := le_of_not_gt h
    have nonpos := mul_nonpos_of_nonneg_of_nonpos hv.le le
    linarith
  have prs : 0<areaDet p r s := by
    obtain ⟨u,v,hu,hv,he⟩ := between_area p r c q s qs
    have prq : areaDet p r q= -areaDet p q r := by unfold areaDet; ring
    rw [area_between_zero p r c pr,prq] at he
    by_contra h
    have le : areaDet p r s≤0 := le_of_not_gt h
    have nonpos := mul_nonpos_of_nonneg_of_nonpos hv.le le
    have positive := mul_pos hu pqr
    nlinarith
  have qrs : 0<areaDet q r s := by
    obtain ⟨u,v,hu,hv,he⟩ := between_area q s c p r pr
    have qsp : areaDet q s p=areaDet p q s := by unfold areaDet; ring
    have qsr : areaDet q s r= -areaDet q r s := by unfold areaDet; ring
    rw [area_between_zero q s c qs,qsp,qsr] at he
    by_contra h
    have le : areaDet q r s≤0 := le_of_not_gt h
    have nonneg := mul_nonneg hv.le (neg_nonneg.mpr le)
    have positive := mul_pos hu pqs
    linarith
  exact ⟨pqr,pqs,prs,qrs⟩

theorem three_corner_boundary (c p q r s a b e : Point)
    (pos : 0<areaDet c p q) (pr : Between c p r) (qs : Between c q s)
    (ma : a=p∨a=q∨a=r∨a=s) (mb : b=p∨b=q∨b=r∨b=s)
    (me : e=p∨e=q∨e=r∨e=s) (ab : a≠b) (ae : a≠e) (be : b≠e) :
    areaDet a b e≠0 ∧ (Between c a b∨Between c a e∨Between c b e) := by
  obtain ⟨pqr,pqs,prs,qrs⟩ := four_corner_areas_positive c p q r s pos pr qs

  have hn0 : areaDet p q r≠0 := by
    have eq : areaDet p q r=areaDet p q r := by unfold areaDet; ring
    rw [eq]
    exact (ne_of_gt pqr)
  have hn1 : areaDet p q s≠0 := by
    have eq : areaDet p q s=areaDet p q s := by unfold areaDet; ring
    rw [eq]
    exact (ne_of_gt pqs)
  have hn2 : areaDet p r q≠0 := by
    have eq : areaDet p r q=-areaDet p q r := by unfold areaDet; ring
    rw [eq]
    exact neg_ne_zero.mpr (ne_of_gt pqr)
  have hn3 : areaDet p r s≠0 := by
    have eq : areaDet p r s=areaDet p r s := by unfold areaDet; ring
    rw [eq]
    exact (ne_of_gt prs)
  have hn4 : areaDet p s q≠0 := by
    have eq : areaDet p s q=-areaDet p q s := by unfold areaDet; ring
    rw [eq]
    exact neg_ne_zero.mpr (ne_of_gt pqs)
  have hn5 : areaDet p s r≠0 := by
    have eq : areaDet p s r=-areaDet p r s := by unfold areaDet; ring
    rw [eq]
    exact neg_ne_zero.mpr (ne_of_gt prs)
  have hn6 : areaDet q p r≠0 := by
    have eq : areaDet q p r=-areaDet p q r := by unfold areaDet; ring
    rw [eq]
    exact neg_ne_zero.mpr (ne_of_gt pqr)
  have hn7 : areaDet q p s≠0 := by
    have eq : areaDet q p s=-areaDet p q s := by unfold areaDet; ring
    rw [eq]
    exact neg_ne_zero.mpr (ne_of_gt pqs)
  have hn8 : areaDet q r p≠0 := by
    have eq : areaDet q r p=areaDet p q r := by unfold areaDet; ring
    rw [eq]
    exact (ne_of_gt pqr)
  have hn9 : areaDet q r s≠0 := by
    have eq : areaDet q r s=areaDet q r s := by unfold areaDet; ring
    rw [eq]
    exact (ne_of_gt qrs)
  have hn10 : areaDet q s p≠0 := by
    have eq : areaDet q s p=areaDet p q s := by unfold areaDet; ring
    rw [eq]
    exact (ne_of_gt pqs)
  have hn11 : areaDet q s r≠0 := by
    have eq : areaDet q s r=-areaDet q r s := by unfold areaDet; ring
    rw [eq]
    exact neg_ne_zero.mpr (ne_of_gt qrs)
  have hn12 : areaDet r p q≠0 := by
    have eq : areaDet r p q=areaDet p q r := by unfold areaDet; ring
    rw [eq]
    exact (ne_of_gt pqr)
  have hn13 : areaDet r p s≠0 := by
    have eq : areaDet r p s=-areaDet p r s := by unfold areaDet; ring
    rw [eq]
    exact neg_ne_zero.mpr (ne_of_gt prs)
  have hn14 : areaDet r q p≠0 := by
    have eq : areaDet r q p=-areaDet p q r := by unfold areaDet; ring
    rw [eq]
    exact neg_ne_zero.mpr (ne_of_gt pqr)
  have hn15 : areaDet r q s≠0 := by
    have eq : areaDet r q s=-areaDet q r s := by unfold areaDet; ring
    rw [eq]
    exact neg_ne_zero.mpr (ne_of_gt qrs)
  have hn16 : areaDet r s p≠0 := by
    have eq : areaDet r s p=areaDet p r s := by unfold areaDet; ring
    rw [eq]
    exact (ne_of_gt prs)
  have hn17 : areaDet r s q≠0 := by
    have eq : areaDet r s q=areaDet q r s := by unfold areaDet; ring
    rw [eq]
    exact (ne_of_gt qrs)
  have hn18 : areaDet s p q≠0 := by
    have eq : areaDet s p q=areaDet p q s := by unfold areaDet; ring
    rw [eq]
    exact (ne_of_gt pqs)
  have hn19 : areaDet s p r≠0 := by
    have eq : areaDet s p r=areaDet p r s := by unfold areaDet; ring
    rw [eq]
    exact (ne_of_gt prs)
  have hn20 : areaDet s q p≠0 := by
    have eq : areaDet s q p=-areaDet p q s := by unfold areaDet; ring
    rw [eq]
    exact neg_ne_zero.mpr (ne_of_gt pqs)
  have hn21 : areaDet s q r≠0 := by
    have eq : areaDet s q r=areaDet q r s := by unfold areaDet; ring
    rw [eq]
    exact (ne_of_gt qrs)
  have hn22 : areaDet s r p≠0 := by
    have eq : areaDet s r p=-areaDet p r s := by unfold areaDet; ring
    rw [eq]
    exact neg_ne_zero.mpr (ne_of_gt prs)
  have hn23 : areaDet s r q≠0 := by
    have eq : areaDet s r q=-areaDet q r s := by unfold areaDet; ring
    rw [eq]
    exact neg_ne_zero.mpr (ne_of_gt qrs)
  rcases ma with ha|ha|ha|ha <;> rcases mb with hb|hb|hb|hb <;> rcases me with he|he|he|he
  all_goals simp only [ha,hb,he] at ab ae be ⊢
  all_goals first
    | exact False.elim (ab rfl)
    | exact False.elim (ae rfl)
    | exact False.elim (be rfl)
    | exact ⟨hn0,Or.inr (Or.inl pr)⟩
    | exact ⟨hn1,Or.inr (Or.inr qs)⟩
    | exact ⟨hn2,Or.inl pr⟩
    | exact ⟨hn3,Or.inl pr⟩
    | exact ⟨hn4,Or.inr (Or.inr qs.symm)⟩
    | exact ⟨hn5,Or.inr (Or.inl pr)⟩
    | exact ⟨hn6,Or.inr (Or.inr pr)⟩
    | exact ⟨hn7,Or.inr (Or.inl qs)⟩
    | exact ⟨hn8,Or.inr (Or.inr pr.symm)⟩
    | exact ⟨hn9,Or.inr (Or.inl qs)⟩
    | exact ⟨hn10,Or.inl qs⟩
    | exact ⟨hn11,Or.inl qs⟩
    | exact ⟨hn12,Or.inl pr.symm⟩
    | exact ⟨hn13,Or.inl pr.symm⟩
    | exact ⟨hn14,Or.inr (Or.inl pr.symm)⟩
    | exact ⟨hn15,Or.inr (Or.inr qs)⟩
    | exact ⟨hn16,Or.inr (Or.inl pr.symm)⟩
    | exact ⟨hn17,Or.inr (Or.inr qs.symm)⟩
    | exact ⟨hn18,Or.inr (Or.inl qs.symm)⟩
    | exact ⟨hn19,Or.inr (Or.inr pr)⟩
    | exact ⟨hn20,Or.inl qs.symm⟩
    | exact ⟨hn21,Or.inl qs.symm⟩
    | exact ⟨hn22,Or.inr (Or.inr pr.symm)⟩
    | exact ⟨hn23,Or.inr (Or.inl qs.symm)⟩

#print axioms three_corner_boundary
end Kobon.UpperOpenMathQuadThreeBoundary
