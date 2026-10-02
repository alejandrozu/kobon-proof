import Kobon.BBLGrid

/-! Exact algebraic description of the tangent-grid parameter tan(pi/20).
This supplies the real interpretation needed by symbolic obstruction data. -/
namespace Kobon.BBLTangentAlgebra
open Real BBLTangentBounds BBLGrid

def quartic (x : ℝ) : ℝ := x^4-4*x^3-14*x^2-4*x+1

theorem half_angle_elimination (t u a : ℝ)
    (h1 : u*(1-t^2)=2*t) (h2 : a*(1-u^2)=2*u)
    (h3 : a*(1+t)=1-t) (ht : t≠1) : quartic t=0 := by
  have h4 : a*((1-t^2)^2-4*t^2)=4*t*(1-t^2) := by
    linear_combination (1-t^2)^2*h2 + (a*(u*(1-t^2)+2*t)+2*(1-t^2))*h1
  have h5 : (1-t)*quartic t=0 := by
    unfold quartic
    linear_combination (1+t)*h4 - ((1-t^2)^2-4*t^2)*h3
  exact (mul_eq_zero.mp h5).resolve_left (by intro h; apply ht; linarith)

theorem tan_quartic : quartic (tan (π/20))=0 := by
  let t := tan (π/20)
  let u := tan (π/10)
  let a := tan (π/5)
  have ht := tan_small (π/20) (by linarith [pi_pos]) (by linarith [pi_pos])
  have h1 : u*(1-t^2)=2*t := by
    have hh := tan_half_identity (π/20) (by linarith [pi_pos]) (by linarith [pi_pos])
    simpa only [show 2*(π/20)=π/10 by ring] using hh
  have h2 : a*(1-u^2)=2*u := by
    have hh := tan_half_identity (π/10) (by linarith [pi_pos]) (by linarith [pi_pos])
    simpa only [show 2*(π/10)=π/5 by ring] using hh
  have hca : cos (π/5)≠0 := ne_of_gt (cos_pos_of_mem_Ioo ⟨by linarith [pi_pos],by linarith [pi_pos]⟩)
  have hct : cos (π/20)≠0 := ne_of_gt (cos_pos_of_mem_Ioo ⟨by linarith [pi_pos],by linarith [pi_pos]⟩)
  have hsum : π/5+π/20=π/4 := by ring
  have hcs : cos (π/5+π/20)≠0 := by
    rw [hsum]
    exact ne_of_gt (cos_pos_of_mem_Ioo ⟨by linarith [pi_pos],by linarith [pi_pos]⟩)
  have hd : 1-a*t≠0 := by
    intro hh
    have hp := tangent_product_identity (π/5) (π/20) hca hct
    change (1-a*t)*(cos (π/5)*cos (π/20))=cos (π/5+π/20) at hp
    rw [hh,zero_mul] at hp
    exact hcs hp.symm
  have hadd : (a+t)/(1-a*t)=1 := by
    have hh := tangent_sum_rational (π/5) (π/20) hca hct hcs
    simpa only [hsum,tan_pi_div_four] using hh
  have h3 : a*(1+t)=1-t := by
    have hh := (div_eq_iff hd).mp hadd
    linarith
  exact half_angle_elimination t u a h1 h2 h3 (ne_of_lt ht.2)

theorem tan_root_interval : (3:ℝ)/20<tan (π/20) ∧ tan (π/20)<17/100 := by
  have hh := tan_1_bounds
  norm_num only [one_mul] at hh
  constructor <;> linarith [hh.1,hh.2]

/-- The quartic has at most one root between zero and one. -/
theorem quartic_root_unique (x y : ℝ) (hx : 0<x) (hx1 : x<1) (hy : 0<y) (hy1 : y<1)
    (hqx : quartic x=0) (hqy : quartic y=0) : x=y := by
  have hxx : x^3≤x^2 := by nlinarith [mul_le_mul_of_nonneg_left (le_of_lt hx1) (sq_nonneg x)]
  have hyy : y^3≤y^2 := by nlinarith [mul_le_mul_of_nonneg_left (le_of_lt hy1) (sq_nonneg y)]
  have hxy : x^2*y≤x^2 := by nlinarith [mul_le_mul_of_nonneg_left (le_of_lt hy1) (sq_nonneg x)]
  have hyx : x*y^2≤y^2 := by nlinarith [mul_le_mul_of_nonneg_left (le_of_lt hx1) (sq_nonneg y)]
  have hn : x^3+x^2*y+x*y^2+y^3-4*x^2-4*x*y-4*y^2-14*x-14*y-4<0 := by
    nlinarith [sq_nonneg x,sq_nonneg y,mul_pos hx hy]
  have hz : (x-y)*(x^3+x^2*y+x*y^2+y^3-4*x^2-4*x*y-4*y^2-14*x-14*y-4)=0 := by
    unfold quartic at hqx hqy
    linear_combination hqx-hqy
  exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_right (ne_of_lt hn))

theorem real_root_characterization (x : ℝ) :
    (quartic x=0 ∧ (3:ℝ)/20<x ∧ x<17/100) ↔ x=tan (π/20) := by
  constructor
  · rintro ⟨hq,hl,hu⟩
    have ht := tan_root_interval
    exact quartic_root_unique x (tan (π/20)) (by linarith) (by linarith)
      (by linarith [ht.1]) (by linarith [ht.2]) hq tan_quartic
  · rintro rfl
    exact ⟨tan_quartic,tan_root_interval⟩

#print axioms tan_quartic
#print axioms real_root_characterization
end Kobon.BBLTangentAlgebra
