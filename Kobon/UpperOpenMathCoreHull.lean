import Kobon.UpperCoreExtraction

/-! A finite planar set has at least three supported points, unless it has
fewer than three points.  Collinear sets have a supporting line at every
point.  The proof uses two coordinate extrema and a third extremum of the
normal to their chord; no polygon or general-position hypothesis is needed. -/
namespace Kobon.UpperOpenMathCoreHull
open Cells FanGeometry UpperVertexBudget UpperCoreExtraction Finset
set_option autoImplicit false
set_option maxHeartbeats 1000000

def HasSupport (P : Finset Point) (c : Point) : Prop :=
  ∃ w : Line ℝ, affineEval w c=0 ∧ (w.a≠0 ∨ w.b≠0) ∧
    ∀ p∈P, 0≤affineEval w p

noncomputable def boundary (P : Finset Point) : Finset Point := by
  classical
  exact P.filter (HasSupport P)

theorem support_at_minimum (P : Finset Point) (w : Line ℝ) (c : Point)
    (valid : w.a≠0 ∨ w.b≠0) (hmin : ∀ p∈P, affineEval w c≤affineEval w p) :
    HasSupport P c := by
  let v : Line ℝ := ⟨w.a,w.b,w.c+affineEval w c⟩
  refine ⟨v,by dsimp [v,affineEval]; ring,valid,?_⟩
  intro p hp
  have h := hmin p hp
  dsimp [v,affineEval] at *
  linarith

theorem support_at_maximum (P : Finset Point) (w : Line ℝ) (c : Point)
    (valid : w.a≠0 ∨ w.b≠0) (hmax : ∀ p∈P, affineEval w p≤affineEval w c) :
    HasSupport P c := by
  let v : Line ℝ := ⟨-w.a,-w.b,-(w.c+affineEval w c)⟩
  refine ⟨v,by dsimp [v,affineEval]; ring,?_,?_⟩
  · rcases valid with h|h
    · exact Or.inl (neg_ne_zero.mpr h)
    · exact Or.inr (neg_ne_zero.mpr h)
  · intro p hp
    have h := hmax p hp
    dsimp [v,affineEval] at *
    linarith

theorem boundary_eq_of_collinear (P : Finset Point) (w : Line ℝ)
    (valid : w.a≠0 ∨ w.b≠0) (hz : ∀ p∈P, affineEval w p=0) : boundary P=P := by
  classical
  apply filter_eq_self.mpr
  intro c hc
  apply support_at_minimum P w c valid
  intro p hp
  rw [hz c hc,hz p hp]

theorem three_supported_points (P : Finset Point) (c d e : Point)
    (hc : c∈P) (hd : d∈P) (he : e∈P)
    (sc : HasSupport P c) (sd : HasSupport P d) (se : HasSupport P e)
    (hcd : c≠d) (hce : c≠e) (hde : d≠e) : 3≤(boundary P).card := by
  classical
  have hsub : ({c,d,e} : Finset Point)⊆boundary P := by
    intro p hp
    simp only [mem_insert,mem_singleton] at hp
    rcases hp with rfl|rfl|rfl
    · exact mem_filter.mpr ⟨hc,sc⟩
    · exact mem_filter.mpr ⟨hd,sd⟩
    · exact mem_filter.mpr ⟨he,se⟩
  have hcard : ({c,d,e} : Finset Point).card=3 := by simp [hcd,hce,hde]
  have h := card_le_card hsub
  rw [hcard] at h
  exact h

/-- The elementary convex-hull boundary count, including every degeneracy. -/
theorem boundary_card (P : Finset Point) : min P.card 3≤(boundary P).card := by
  classical
  by_cases hne : P.Nonempty
  · obtain ⟨c,hc,hmin⟩ := exists_min_image P (fun p : Point => p.1) hne
    obtain ⟨d,hd,hmax⟩ := exists_max_image P (fun p : Point => p.1) hne
    let x : Line ℝ := ⟨1,0,0⟩
    have sx : x.a≠0 ∨ x.b≠0 := Or.inl (by norm_num [x])
    have sc : HasSupport P c := support_at_minimum P x c sx (by
      intro p hp
      simpa only [x,affineEval,one_mul,zero_mul,add_zero,sub_zero] using hmin p hp)
    have sd : HasSupport P d := support_at_maximum P x d sx (by
      intro p hp
      simpa only [x,affineEval,one_mul,zero_mul,add_zero,sub_zero] using hmax p hp)
    by_cases he : c.1=d.1
    · let w : Line ℝ := ⟨1,0,c.1⟩
      have hz (p : Point) (hp : p∈P) : affineEval w p=0 := by
        have h1 := hmin p hp
        have h2 := hmax p hp
        dsimp [w,affineEval]
        rw [← he] at h2
        linarith
      rw [boundary_eq_of_collinear P w (Or.inl (by norm_num [w])) hz]
      exact Nat.min_le_left _ _
    · have hcd : c≠d := by intro h; exact he (congrArg Prod.fst h)
      let w : Line ℝ := ⟨d.2-c.2,c.1-d.1,(d.2-c.2)*c.1+(c.1-d.1)*c.2⟩
      have valid : w.a≠0 ∨ w.b≠0 := Or.inr (sub_ne_zero.mpr he)
      have hcw : affineEval w c=0 := by dsimp [w,affineEval]; ring
      have hdw : affineEval w d=0 := by dsimp [w,affineEval]; ring
      by_cases hz : ∀ p∈P, affineEval w p=0
      · rw [boundary_eq_of_collinear P w valid hz]
        exact Nat.min_le_left _ _
      · push_neg at hz
        obtain ⟨p,hp,hpne⟩ := hz
        rcases lt_or_gt_of_ne hpne with hneg|hpos
        · obtain ⟨e,he,hE⟩ := exists_min_image P (affineEval w) hne
          have hEneg : affineEval w e<0 := lt_of_le_of_lt (hE p hp) hneg
          have hce : c≠e := by intro h; rw [← h,hcw] at hEneg; linarith
          have hde : d≠e := by intro h; rw [← h,hdw] at hEneg; linarith
          have se := support_at_minimum P w e valid hE
          exact (Nat.min_le_right _ _).trans (three_supported_points P c d e hc hd he sc sd se hcd hce hde)
        · obtain ⟨e,he,hE⟩ := exists_max_image P (affineEval w) hne
          have hEpos : 0<affineEval w e := lt_of_lt_of_le hpos (hE p hp)
          have hce : c≠e := by intro h; rw [← h,hcw] at hEpos; linarith
          have hde : d≠e := by intro h; rw [← h,hdw] at hEpos; linarith
          have se := support_at_maximum P w e valid hE
          exact (Nat.min_le_right _ _).trans (three_supported_points P c d e hc hd he sc sd se hcd hce hde)
  · have hp : P=∅ := not_nonempty_iff_eq_empty.mp hne
    simp [hp]

#print axioms boundary_card
end Kobon.UpperOpenMathCoreHull
