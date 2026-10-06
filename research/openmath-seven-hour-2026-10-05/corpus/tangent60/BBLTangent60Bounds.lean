import Kobon.BBLTangent48Bounds

/-! Rational enclosures for the actual denominator-60 tangent grid.
Generated proof text is checked by Lean: no floating values or evaluation
oracle occurs in the theorem dependency. -/
namespace Kobon.BBLTangent60Bounds
open Real BBLTangentBounds
set_option maxHeartbeats 0

theorem not_pole {x : ℝ} (hl : -(π/2)<x) (hu : x<π/2) :
    ∀ k : ℤ, x≠(2*k+1)*π/2 := by
  have hc : cos x≠0 := ne_of_gt (cos_pos_of_mem_Ioo ⟨hl,hu⟩)
  intro k he
  exact hc (cos_eq_zero_iff.mpr ⟨k,he⟩)

theorem subtraction_bounds (A B Alo Ahi Blo Bhi L U : ℝ)
    (hA : 0≤A) (hB : 0≤B) (hAl : Alo≤A) (hAu : A≤Ahi)
    (hBl : Blo≤B) (hBu : B≤Bhi) (hBlo : 0≤Blo) (hAhi : 0≤Ahi)
    (hL : 0≤L) (hU : 0≤U)
    (hl : L*(1+Ahi*Bhi)≤Alo-Bhi)
    (hu : Ahi-Blo≤U*(1+Alo*Blo)) :
    L≤(A-B)/(1+A*B) ∧ (A-B)/(1+A*B)≤U := by
  have hd : 0<1+A*B := by positivity
  have hlo : Alo*Blo≤A*B := mul_le_mul hAl hBl hBlo hA
  have hhi : A*B≤Ahi*Bhi := mul_le_mul hAu hBu hB hAhi
  constructor
  · apply (le_div_iff₀ hd).mpr
    calc
      L*(1+A*B)≤L*(1+Ahi*Bhi) := mul_le_mul_of_nonneg_left (by linarith) hL
      _≤Alo-Bhi := hl
      _≤A-B := sub_le_sub hAl hBu
  · apply (div_le_iff₀ hd).mpr
    calc
      A-B≤Ahi-Blo := sub_le_sub hAu hBl
      _≤U*(1+Alo*Blo) := hu
      _≤U*(1+A*B) := mul_le_mul_of_nonneg_left (by linarith) hU

theorem tan_3_bounds : ((79192220162268146919441546347:ℝ)/500000000000000000000000000000)≤tan (3*π/60) ∧ tan (3*π/60)≤((31676888064907258767776618539:ℝ)/200000000000000000000000000000) := by
  have heq : 3*π/60=1*π/20 := by ring
  rw [heq]
  convert BBLTangentBounds.tan_1_bounds using 1 <;> norm_num

theorem tan_6_bounds : ((3249196962329063261558714122151344649549:ℝ)/10000000000000000000000000000000000000000)≤tan (6*π/60) ∧ tan (6*π/60)≤((64983939246581265231174282443026892991:ℝ)/200000000000000000000000000000000000000) := by
  have heq : 6*π/60=2*π/20 := by ring
  rw [heq]
  convert BBLTangentBounds.tan_2_bounds using 1 <;> norm_num

theorem tan_9_bounds : ((407620359595543048410965529:ℝ)/800000000000000000000000000)≤tan (9*π/60) ∧ tan (9*π/60)≤((509525449494428810513706911251:ℝ)/1000000000000000000000000000000) := by
  have heq : 9*π/60=3*π/20 := by ring
  rw [heq]
  convert BBLTangentBounds.tan_3_bounds using 1 <;> norm_num

theorem tan_10_bounds : ((2886751345948128822545743902509787278238008756350634380093011632419887:ℝ)/5000000000000000000000000000000000000000000000000000000000000000000000)≤tan (10*π/60) ∧ tan (10*π/60)≤((5773502691896257645091487805019574556476017512701268760186023264839779:ℝ)/10000000000000000000000000000000000000000000000000000000000000000000000) := by
  have heq : 10*π/60=1*π/6 := by ring
  rw [heq]
  convert BBLTangent48Bounds.tan_6_1_bounds using 1 <;> norm_num

theorem tan_12_bounds : ((45408908000335055368466672342538671851:ℝ)/62500000000000000000000000000000000000)≤tan (12*π/60) ∧ tan (12*π/60)≤((7265425280053608858954667574806187496161:ℝ)/10000000000000000000000000000000000000000) := by
  have heq : 12*π/60=4*π/20 := by ring
  rw [heq]
  convert BBLTangentBounds.tan_4_bounds using 1 <;> norm_num

theorem tan_15_bounds : ((1:ℝ)/1)≤tan (15*π/60) ∧ tan (15*π/60)≤((1:ℝ)/1) := by
  have heq : 15*π/60=π/4 := by ring
  rw [heq]
  rw [tan_pi_div_four]
  norm_num

theorem tan_18_bounds : ((137638192047117353820720958191088767:ℝ)/100000000000000000000000000000000000)≤tan (18*π/60) ∧ tan (18*π/60)≤((1075298375368104326724382485867881:ℝ)/781250000000000000000000000000000) := by
  have heq : 18*π/60=6*π/20 := by ring
  rw [heq]
  convert BBLTangentBounds.tan_6_bounds using 1 <;> norm_num

theorem tan_20_bounds : ((173205080756887729352744634150587236694280525381038062805580697945193301690880001:ℝ)/100000000000000000000000000000000000000000000000000000000000000000000000000000000)≤tan (20*π/60) ∧ tan (20*π/60)≤((86602540378443864676372317075293618347140262690519031402790348972596650845440003:ℝ)/50000000000000000000000000000000000000000000000000000000000000000000000000000000) := by
  have heq : 20*π/60=1*π/3 := by ring
  rw [heq]
  convert BBLTangent48Bounds.tan_3_1_bounds using 1 <;> norm_num

theorem tan_21_bounds : ((4906526263762876455761601:ℝ)/2500000000000000000000000)≤tan (21*π/60) ∧ tan (21*π/60)≤((3925221011010301164609281:ℝ)/2000000000000000000000000) := by
  have heq : 21*π/60=7*π/20 := by ring
  rw [heq]
  convert BBLTangentBounds.tan_7_bounds using 1 <;> norm_num

theorem tan_24_bounds : ((153884176858762670128514528801845491:ℝ)/50000000000000000000000000000000000)≤tan (24*π/60) ∧ tan (24*π/60)≤((307768353717525340257029057603690983:ℝ)/100000000000000000000000000000000000) := by
  have heq : 24*π/60=8*π/20 := by ring
  rw [heq]
  convert BBLTangentBounds.tan_8_bounds using 1 <;> norm_num

theorem tan_27_bounds : ((31568757573375215494897321:ℝ)/5000000000000000000000000)≤tan (27*π/60) ∧ tan (27*π/60)≤((63137515146750430989794643:ℝ)/10000000000000000000000000) := by
  have heq : 27*π/60=9*π/20 := by ring
  rw [heq]
  convert BBLTangentBounds.tan_9_bounds using 1 <;> norm_num

theorem tan_5_bounds : ((267949192431122706472553658494127633057194746189619371944191:ℝ)/1000000000000000000000000000000000000000000000000000000000000)≤tan (5*π/60) ∧ tan (5*π/60)≤((66987298107780676618138414623531908264298686547404842986049:ℝ)/250000000000000000000000000000000000000000000000000000000000) := by
  have heq : 5*π/60=1*π/12 := by ring
  rw [heq]
  convert BBLTangent48Bounds.tan_12_1_bounds using 1 <;> norm_num

theorem tan_2_bounds : ((52552117632838231255751:ℝ)/500000000000000000000000)≤tan (2*π/60) ∧ tan (2*π/60)≤((105104235265676462511503:ℝ)/1000000000000000000000000) := by
  have heq : 2*π/60=12*π/60-10*π/60 := by ring
  rw [heq,tan_sub' ⟨not_pole (by linarith [pi_pos]) (by linarith [pi_pos]),not_pole (by linarith [pi_pos]) (by linarith [pi_pos])⟩]
  obtain ⟨hAl,hAu⟩ := tan_12_bounds
  obtain ⟨hBl,hBu⟩ := tan_10_bounds
  exact subtraction_bounds _ _ ((45408908000335055368466672342538671851:ℝ)/62500000000000000000000000000000000000) ((7265425280053608858954667574806187496161:ℝ)/10000000000000000000000000000000000000000) ((2886751345948128822545743902509787278238008756350634380093011632419887:ℝ)/5000000000000000000000000000000000000000000000000000000000000000000000) ((5773502691896257645091487805019574556476017512701268760186023264839779:ℝ)/10000000000000000000000000000000000000000000000000000000000000000000000) _ _
    (by linarith) (by linarith) hAl hAu hBl hBu (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem tan_1_bounds : ((131019448207603010097:ℝ)/2500000000000000000000)≤tan (1*π/60) ∧ tan (1*π/60)≤((524077792830412040389:ℝ)/10000000000000000000000) := by
  obtain ⟨hp,hu⟩ := tan_small (1*π/60) (by linarith [pi_pos]) (by linarith [pi_pos])
  have hid := tan_half_identity (1*π/60) (by linarith [pi_pos]) (by linarith [pi_pos])
  have heq : 2*(1*π/60)=2*π/60 := by ring
  rw [heq] at hid
  obtain ⟨hAl,hAu⟩ := tan_2_bounds
  exact half_bounds _ _ _ _ ((52552117632838231255751:ℝ)/500000000000000000000000) ((105104235265676462511503:ℝ)/1000000000000000000000000) hp hu (by linarith) hAl hAu
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hid (by norm_num) (by norm_num)

theorem tan_4_bounds : ((212556561670022125259591:ℝ)/1000000000000000000000000)≤tan (4*π/60) ∧ tan (4*π/60)≤((26569570208752765657449:ℝ)/125000000000000000000000) := by
  have heq : 4*π/60=10*π/60-6*π/60 := by ring
  rw [heq,tan_sub' ⟨not_pole (by linarith [pi_pos]) (by linarith [pi_pos]),not_pole (by linarith [pi_pos]) (by linarith [pi_pos])⟩]
  obtain ⟨hAl,hAu⟩ := tan_10_bounds
  obtain ⟨hBl,hBu⟩ := tan_6_bounds
  exact subtraction_bounds _ _ ((2886751345948128822545743902509787278238008756350634380093011632419887:ℝ)/5000000000000000000000000000000000000000000000000000000000000000000000) ((5773502691896257645091487805019574556476017512701268760186023264839779:ℝ)/10000000000000000000000000000000000000000000000000000000000000000000000) ((3249196962329063261558714122151344649549:ℝ)/10000000000000000000000000000000000000000) ((64983939246581265231174282443026892991:ℝ)/200000000000000000000000000000000000000) _ _
    (by linarith) (by linarith) hAl hAu hBl hBu (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem tan_7_bounds : ((47983004379426974496431:ℝ)/125000000000000000000000)≤tan (7*π/60) ∧ tan (7*π/60)≤((383864035035415795971449:ℝ)/1000000000000000000000000) := by
  have heq : 7*π/60=10*π/60-3*π/60 := by ring
  rw [heq,tan_sub' ⟨not_pole (by linarith [pi_pos]) (by linarith [pi_pos]),not_pole (by linarith [pi_pos]) (by linarith [pi_pos])⟩]
  obtain ⟨hAl,hAu⟩ := tan_10_bounds
  obtain ⟨hBl,hBu⟩ := tan_3_bounds
  exact subtraction_bounds _ _ ((2886751345948128822545743902509787278238008756350634380093011632419887:ℝ)/5000000000000000000000000000000000000000000000000000000000000000000000) ((5773502691896257645091487805019574556476017512701268760186023264839779:ℝ)/10000000000000000000000000000000000000000000000000000000000000000000000) ((79192220162268146919441546347:ℝ)/500000000000000000000000000000) ((31676888064907258767776618539:ℝ)/200000000000000000000000000000) _ _
    (by linarith) (by linarith) hAl hAu hBl hBu (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem tan_8_bounds : ((222614342654268081961183:ℝ)/500000000000000000000000)≤tan (8*π/60) ∧ tan (8*π/60)≤((6956698207945877561287:ℝ)/15625000000000000000000) := by
  have heq : 8*π/60=12*π/60-4*π/60 := by ring
  rw [heq,tan_sub' ⟨not_pole (by linarith [pi_pos]) (by linarith [pi_pos]),not_pole (by linarith [pi_pos]) (by linarith [pi_pos])⟩]
  obtain ⟨hAl,hAu⟩ := tan_12_bounds
  obtain ⟨hBl,hBu⟩ := tan_4_bounds
  exact subtraction_bounds _ _ ((45408908000335055368466672342538671851:ℝ)/62500000000000000000000000000000000000) ((7265425280053608858954667574806187496161:ℝ)/10000000000000000000000000000000000000000) ((212556561670022125259591:ℝ)/1000000000000000000000000) ((26569570208752765657449:ℝ)/125000000000000000000000) _ _
    (by linarith) (by linarith) hAl hAu hBl hBu (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem tan_11_bounds : ((649407593197510576981929:ℝ)/1000000000000000000000000)≤tan (11*π/60) ∧ tan (11*π/60)≤((81175949149688822122759:ℝ)/125000000000000000000000) := by
  have heq : 11*π/60=12*π/60-1*π/60 := by ring
  rw [heq,tan_sub' ⟨not_pole (by linarith [pi_pos]) (by linarith [pi_pos]),not_pole (by linarith [pi_pos]) (by linarith [pi_pos])⟩]
  obtain ⟨hAl,hAu⟩ := tan_12_bounds
  obtain ⟨hBl,hBu⟩ := tan_1_bounds
  exact subtraction_bounds _ _ ((45408908000335055368466672342538671851:ℝ)/62500000000000000000000000000000000000) ((7265425280053608858954667574806187496161:ℝ)/10000000000000000000000000000000000000000) ((131019448207603010097:ℝ)/2500000000000000000000) ((524077792830412040389:ℝ)/10000000000000000000000) _ _
    (by linarith) (by linarith) hAl hAu hBl hBu (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem tan_13_bounds : ((80978403319500714803699:ℝ)/100000000000000000000000)≤tan (13*π/60) ∧ tan (13*π/60)≤((6326437759335993344039:ℝ)/7812500000000000000000) := by
  have heq : 13*π/60=15*π/60-2*π/60 := by ring
  rw [heq,tan_sub' ⟨not_pole (by linarith [pi_pos]) (by linarith [pi_pos]),not_pole (by linarith [pi_pos]) (by linarith [pi_pos])⟩]
  obtain ⟨hAl,hAu⟩ := tan_15_bounds
  obtain ⟨hBl,hBu⟩ := tan_2_bounds
  exact subtraction_bounds _ _ ((1:ℝ)/1) ((1:ℝ)/1) ((52552117632838231255751:ℝ)/500000000000000000000000) ((105104235265676462511503:ℝ)/1000000000000000000000000) _ _
    (by linarith) (by linarith) hAl hAu hBl hBu (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem tan_14_bounds : ((900404044297839945120307:ℝ)/1000000000000000000000000)≤tan (14*π/60) ∧ tan (14*π/60)≤((112550505537229993140061:ℝ)/125000000000000000000000) := by
  have heq : 14*π/60=15*π/60-1*π/60 := by ring
  rw [heq,tan_sub' ⟨not_pole (by linarith [pi_pos]) (by linarith [pi_pos]),not_pole (by linarith [pi_pos]) (by linarith [pi_pos])⟩]
  obtain ⟨hAl,hAu⟩ := tan_15_bounds
  obtain ⟨hBl,hBu⟩ := tan_1_bounds
  exact subtraction_bounds _ _ ((1:ℝ)/1) ((1:ℝ)/1) ((131019448207603010097:ℝ)/2500000000000000000000) ((524077792830412040389:ℝ)/10000000000000000000000) _ _
    (by linarith) (by linarith) hAl hAu hBl hBu (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem tan_16_bounds : ((55530625741459643507:ℝ)/50000000000000000000)≤tan (16*π/60) ∧ tan (16*π/60)≤((22212250296583857403:ℝ)/20000000000000000000) := by
  have heq : 16*π/60=π/2-14*π/60 := by ring
  rw [heq,tan_pi_div_two_sub]
  obtain ⟨hl,hu⟩ := tan_14_bounds
  have hp : 0<tan (14*π/60) := by linarith
  apply inverse_bounds _ _ _ hp (by norm_num) (by norm_num)
  · nlinarith
  · nlinarith

theorem tan_17_bounds : ((24697943130701027971:ℝ)/20000000000000000000)≤tan (17*π/60) ∧ tan (17*π/60)≤((7718107228344071241:ℝ)/6250000000000000000) := by
  have heq : 17*π/60=π/2-13*π/60 := by ring
  rw [heq,tan_pi_div_two_sub]
  obtain ⟨hl,hu⟩ := tan_13_bounds
  have hp : 0<tan (13*π/60) := by linarith
  apply inverse_bounds _ _ _ hp (by norm_num) (by norm_num)
  · nlinarith
  · nlinarith

theorem tan_19_bounds : ((76993248190729145241:ℝ)/50000000000000000000)≤tan (19*π/60) ∧ tan (19*π/60)≤((153986496381458290483:ℝ)/100000000000000000000) := by
  have heq : 19*π/60=π/2-11*π/60 := by ring
  rw [heq,tan_pi_div_two_sub]
  obtain ⟨hl,hu⟩ := tan_11_bounds
  have hp : 0<tan (11*π/60) := by linarith
  apply inverse_bounds _ _ _ hp (by norm_num) (by norm_num)
  · nlinarith
  · nlinarith

theorem tan_22_bounds : ((28075459673802700677:ℝ)/12500000000000000000)≤tan (22*π/60) ∧ tan (22*π/60)≤((224603677390421605417:ℝ)/100000000000000000000) := by
  have heq : 22*π/60=π/2-8*π/60 := by ring
  rw [heq,tan_pi_div_two_sub]
  obtain ⟨hl,hu⟩ := tan_8_bounds
  have hp : 0<tan (8*π/60) := by linarith
  apply inverse_bounds _ _ _ hp (by norm_num) (by norm_num)
  · nlinarith
  · nlinarith

theorem tan_23_bounds : ((2084071251755041229:ℝ)/800000000000000000)≤tan (23*π/60) ∧ tan (23*π/60)≤((130254453234690076813:ℝ)/50000000000000000000) := by
  have heq : 23*π/60=π/2-7*π/60 := by ring
  rw [heq,tan_pi_div_two_sub]
  obtain ⟨hl,hu⟩ := tan_7_bounds
  have hp : 0<tan (7*π/60) := by linarith
  apply inverse_bounds _ _ _ hp (by norm_num) (by norm_num)
  · nlinarith
  · nlinarith

theorem tan_25_bounds : ((46650635094610966169:ℝ)/12500000000000000000)≤tan (25*π/60) ∧ tan (25*π/60)≤((373205080756887729353:ℝ)/100000000000000000000) := by
  have heq : 25*π/60=π/2-5*π/60 := by ring
  rw [heq,tan_pi_div_two_sub]
  obtain ⟨hl,hu⟩ := tan_5_bounds
  have hp : 0<tan (5*π/60) := by linarith
  apply inverse_bounds _ _ _ hp (by norm_num) (by norm_num)
  · nlinarith
  · nlinarith

theorem tan_26_bounds : ((235231505473922711679:ℝ)/50000000000000000000)≤tan (26*π/60) ∧ tan (26*π/60)≤((470463010947845423359:ℝ)/100000000000000000000) := by
  have heq : 26*π/60=π/2-4*π/60 := by ring
  rw [heq,tan_pi_div_two_sub]
  obtain ⟨hl,hu⟩ := tan_4_bounds
  have hp : 0<tan (4*π/60) := by linarith
  apply inverse_bounds _ _ _ hp (by norm_num) (by norm_num)
  · nlinarith
  · nlinarith

theorem tan_28_bounds : ((118929555677782311621:ℝ)/12500000000000000000)≤tan (28*π/60) ∧ tan (28*π/60)≤((951436445422258492969:ℝ)/100000000000000000000) := by
  have heq : 28*π/60=π/2-2*π/60 := by ring
  rw [heq,tan_pi_div_two_sub]
  obtain ⟨hl,hu⟩ := tan_2_bounds
  have hp : 0<tan (2*π/60) := by linarith
  apply inverse_bounds _ _ _ hp (by norm_num) (by norm_num)
  · nlinarith
  · nlinarith

theorem tan_29_bounds : ((1908113668772821106337:ℝ)/100000000000000000000)≤tan (29*π/60) ∧ tan (29*π/60)≤((1908113668772821106341:ℝ)/100000000000000000000) := by
  have heq : 29*π/60=π/2-1*π/60 := by ring
  rw [heq,tan_pi_div_two_sub]
  obtain ⟨hl,hu⟩ := tan_1_bounds
  have hp : 0<tan (1*π/60) := by linarith
  apply inverse_bounds _ _ _ hp (by norm_num) (by norm_num)
  · nlinarith
  · nlinarith

#print axioms tan_1_bounds
#print axioms tan_29_bounds
end Kobon.BBLTangent60Bounds
