import Kobon.OpenMathBoundaryRays

/-! Tangent-ray derivatives connect actual terminal signs to the original
exterior insertion predicate. Positive normal projections determine the
chosen forward side of both supporting lines. -/
namespace Kobon.OpenMathBoundaryVisibility
open Cells FanGeometry Exterior OpenMathBoundaryNormals
set_option autoImplicit false
set_option maxHeartbeats 0

theorem tangent_derivative (r l w : Line ℝ) (d : Point)
    (hl : projection l d=0) (hw : det w l≠0) (hp : projection w d≠0) :
    derivative r l w=projection r d/projection w d := by
  have he : det w l*projection r d=det r l*projection w d := by
    have hid : det w l*projection r d-det r l*projection w d=
        det w r*projection l d := by dsimp [det,projection]; ring
    rw [hl,mul_zero] at hid
    exact sub_eq_zero.mp hid
  dsimp [derivative]
  apply (div_eq_div_iff hw hp).mpr
  calc
    det r l*projection w d=det w l*projection r d := he.symm
    _=projection r d*det w l := mul_comm _ _

@[simp] theorem derivative_self (l w : Line ℝ) : derivative l l w=0 := by
  have hd : det l l=0 := by dsimp [det]; ring
  simp [derivative,hd]

theorem pair_visible_of_terminal_signs (n : ℕ) (L : ℕ → Line ℝ)
    (hp : NoParallel n L) (hs : NoConcurrent n L)
    (i j : Fin n) (hij : i<j) (w : Line ℝ) (hw : Admissible n L w)
    (d e : Point)
    (hdi : projection (L i) d=0) (hej : projection (L j) e=0)
    (hd : TerminalSigns n L (intersection (L i) (L j)) d)
    (he : TerminalSigns n L (intersection (L i) (L j)) e)
    (hwd : 0<projection w d) (hwe : 0<projection w e) :
    VisiblePair n L w ⟨i.val,j.val,n⟩ := by
  have hiw : det w (L i)≠0 := by
    have h := hw i
    have heq : det w (L i)= -det (L i) w := by dsimp [det]; ring
    rw [heq]
    exact neg_ne_zero.mpr h
  have hjw : det w (L j)≠0 := by
    have h := hw j
    have heq : det w (L j)= -det (L j) w := by dsimp [det]; ring
    rw [heq]
    exact neg_ne_zero.mpr h
  have ho := UpperSimpleOptimality.ordinary_intersection n L hp hs i j (ne_of_lt hij)
  have hip : affineEval (L i) (intersection (L i) (L j))=0 :=
    intersection_on_left _ _ (hp i j hij)
  have hjp : affineEval (L j) (intersection (L i) (L j))=0 :=
    intersection_on_right _ _ (hp i j hij)
  refine ⟨hij,j.isLt,rfl,?_⟩
  intro r
  by_cases hri : r=i
  · subst r
    rw [hip,derivative_self]
    by_cases hj : 0≤derivative (L i) (L j) w
    · exact Or.inl ⟨le_rfl,le_rfl,hj⟩
    · exact Or.inr ⟨le_rfl,le_rfl,le_of_not_ge hj⟩
  by_cases hrj : r=j
  · subst r
    rw [hjp,derivative_self]
    by_cases hi : 0≤derivative (L j) (L i) w
    · exact Or.inl ⟨le_rfl,hi,le_rfl⟩
    · exact Or.inr ⟨le_rfl,le_of_not_ge hi,le_rfl⟩
  have hrp : affineEval (L r) (intersection (L i) (L j))≠0 := by
    intro hz
    obtain ⟨a,b,hab,hspan⟩ := ho
    have hr := (hspan r).mp hz
    have hi := (hspan i).mp hip
    have hj := (hspan j).mp hjp
    have hne : i≠j := ne_of_lt hij
    rcases hi with hi|hi <;> rcases hj with hj|hj <;> rcases hr with hr|hr
    all_goals first
      | exact hne (hi.trans hj.symm)
      | exact hri (hr.trans hi.symm)
      | exact hrj (hr.trans hj.symm)
  have hdpos := hd r hrp
  have hepos := he r hrp
  rw [tangent_derivative (L r) (L i) w d hdi hiw (ne_of_gt hwd),
    tangent_derivative (L r) (L j) w e hej hjw (ne_of_gt hwe)]
  rcases lt_or_gt_of_ne hrp with hneg|hpos
  · right
    have hpd : projection (L r) d<0 :=
      ((mul_pos_iff.mp hdpos).resolve_left (by rintro ⟨ha,_⟩; linarith)).2
    have hpe : projection (L r) e<0 :=
      ((mul_pos_iff.mp hepos).resolve_left (by rintro ⟨ha,_⟩; linarith)).2
    exact ⟨hneg.le,(div_neg_of_neg_of_pos hpd hwd).le,(div_neg_of_neg_of_pos hpe hwe).le⟩
  · left
    have hpd : 0<projection (L r) d := (mul_pos_iff_of_pos_left hpos).mp hdpos
    have hpe : 0<projection (L r) e := (mul_pos_iff_of_pos_left hpos).mp hepos
    exact ⟨hpos.le,(div_pos hpd hwd).le,(div_pos hpe hwe).le⟩

#print axioms tangent_derivative
#print axioms pair_visible_of_terminal_signs

end Kobon.OpenMathBoundaryVisibility
