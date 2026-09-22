import Kobon.FurediPalasti
import Kobon.ShiftedCount

/-! Phase-shifted classical construction. The improved count is proved for every order. -/
namespace Kobon.ShiftedFurediPalasti
open FurediPalasti (line det_line eval_line oriented_line)

noncomputable def angle (n i : ℕ) : ℝ := ((i:ℝ)+1/6)/(n:ℝ)*Real.pi
noncomputable def arrangement (n i : ℕ) : Line ℝ := line (angle n i)

theorem angle_pos {n i : ℕ} (hn : 0 < n) : 0 < angle n i := by
  unfold angle
  positivity

theorem angle_lt_pi {n i : ℕ} (hi : i < n) : angle n i < Real.pi := by
  have hn : (0:ℝ)<n := by exact_mod_cast (show 0 < n by omega)
  have h : (i:ℝ)+1/6 < n := by
    have : (i:ℝ)+1 ≤ n := by exact_mod_cast hi
    linarith
  unfold angle
  exact mul_lt_of_lt_one_left Real.pi_pos ((div_lt_one hn).mpr h)

theorem angle_strictMono {n i j : ℕ} (hn : 0 < n) (hij : i < j) :
    angle n i < angle n j := by
  unfold angle
  gcongr

theorem sin_diff_neg {n i j : ℕ} (hij : i < j) (hj : j < n) :
    Real.sin (angle n i-angle n j)<0 := by
  have hn : 0 < n := by omega
  apply Real.sin_neg_of_neg_of_neg_pi_lt
  · linarith [angle_strictMono hn hij]
  · linarith [angle_pos (i:=i) hn,angle_lt_pi hj]

theorem sin_diff_pos {n i j : ℕ} (hij : i < j) (hj : j < n) :
    0 < Real.sin (angle n j-angle n i) := by
  have he : angle n j-angle n i = -(angle n i-angle n j) := by ring
  rw [he,Real.sin_neg]
  linarith [sin_diff_neg hij hj]

theorem noParallel (n : ℕ) : NoParallel n (arrangement n) := by
  intro i j hij
  rw [arrangement,arrangement,det_line]
  exact ne_of_lt (sin_diff_neg hij j.isLt)

noncomputable def sumAngle (n s : ℕ) : ℝ := ((s:ℝ)+1/2)/(n:ℝ)*Real.pi

theorem angle_sum (n i j k : ℕ) :
    angle n i+angle n j+angle n k=sumAngle n (i+j+k) := by
  simp only [angle,sumAngle,Nat.cast_add]
  ring

theorem sumAngle_band {n s b : ℕ} (hn : 0 < n)
    (hlo : b*n ≤ s) (hhi : s+1 ≤ (b+1)*n) :
    (b:ℝ)*Real.pi < sumAngle n s ∧ sumAngle n s < ((b:ℝ)+1)*Real.pi := by
  have hnR : (0:ℝ)<n := by exact_mod_cast hn
  have hloR : (b:ℝ)*n ≤ s := by exact_mod_cast hlo
  have hhiR : (s:ℝ)+1 ≤ (b+1)*n := by exact_mod_cast hhi
  have hl : (b:ℝ) < ((s:ℝ)+1/2)/n := (lt_div_iff₀ hnR).mpr (by linarith)
  have hh : ((s:ℝ)+1/2)/n < (b:ℝ)+1 := (div_lt_iff₀ hnR).mpr (by linarith)
  exact ⟨mul_lt_mul_of_pos_right hl Real.pi_pos,mul_lt_mul_of_pos_right hh Real.pi_pos⟩

theorem sum_sin_pos0 {n s : ℕ} (hn : 0 < n) (hs : s+1≤n) :
    0 < Real.sin (sumAngle n s) := by
  have h := sumAngle_band (b:=0) hn (by simp) (by simpa using hs)
  simp only [Nat.cast_zero,zero_mul,zero_add,one_mul] at h
  exact Real.sin_pos_of_pos_of_lt_pi h.1 h.2

theorem sum_sin_neg1 {n s : ℕ} (hn : 0 < n) (hl : n≤s) (hh : s+1≤2*n) :
    Real.sin (sumAngle n s)<0 := by
  have h := sumAngle_band (b:=1) hn (by simpa using hl) (by simpa using hh)
  norm_num at h
  have hp := Real.sin_pos_of_pos_of_lt_pi
    (show 0 < sumAngle n s-Real.pi by linarith)
    (show sumAngle n s-Real.pi < Real.pi by linarith)
  rw [Real.sin_sub_pi] at hp
  linarith

theorem sum_sin_pos2 {n s : ℕ} (hn : 0 < n) (hl : 2*n≤s) (hh : s+1≤3*n) :
    0 < Real.sin (sumAngle n s) := by
  have h := sumAngle_band (b:=2) hn (by simpa using hl) (by simpa using hh)
  norm_num at h
  have hp := Real.sin_pos_of_pos_of_lt_pi
    (show 0 < sumAngle n s-2*Real.pi by linarith)
    (show sumAngle n s-2*Real.pi < Real.pi by linarith)
  simpa only [Real.sin_sub_two_pi] using hp

def LowBand (n s : ℕ) : Prop := s+1=n ∨ s=n
def HighBand (n s : ℕ) : Prop := s+1=2*n ∨ s=2*n

theorem low_before {n a b c r : ℕ} (hn : 3≤n)
    (hs : LowBand n (a+b+c)) (hr : r < c) :
    0 < Real.sin (sumAngle n (a+b+r)) := by
  apply sum_sin_pos0 (by omega)
  unfold LowBand at hs
  omega

theorem low_after {n a b c r : ℕ} (hn : 3≤n) (hrn : r < n)
    (hs : LowBand n (a+b+c)) (hr : c < r) :
    Real.sin (sumAngle n (a+b+r))<0 := by
  apply sum_sin_neg1 (by omega)
  · unfold LowBand at hs; omega
  · unfold LowBand at hs; omega

theorem high_before {n a b c r : ℕ} (hn : 3≤n) (hcn : c < n)
    (hs : HighBand n (a+b+c)) (hr : r < c) :
    Real.sin (sumAngle n (a+b+r))<0 := by
  apply sum_sin_neg1 (by omega)
  · unfold HighBand at hs; omega
  · unfold HighBand at hs; omega

theorem high_after {n a b c r : ℕ} (hn : 3≤n) (hrn : r < n)
    (hs : HighBand n (a+b+c)) (hr : c < r) :
    0 < Real.sin (sumAngle n (a+b+r)) := by
  apply sum_sin_pos2 (by omega)
  · unfold HighBand at hs; omega
  · unfold HighBand at hs; omega

theorem selected_sum_nonzero {n s : ℕ} (hn : 3≤n)
    (hs : LowBand n s ∨ HighBand n s) : Real.sin (sumAngle n s)≠0 := by
  rcases hs with (hs|hs) | (hs|hs)
  · exact ne_of_gt (sum_sin_pos0 (by omega) (by omega))
  · exact ne_of_lt (sum_sin_neg1 (by omega) (by omega) (by omega))
  · exact ne_of_lt (sum_sin_neg1 (by omega) (by omega) (by omega))
  · exact ne_of_gt (sum_sin_pos2 (by omega) (by omega) (by omega))

private theorem sign_ppp {a b c d : ℝ} (ha : 0≤a) (hb : 0≤b) (hc : 0≤c) (hd : 0≤d) :
    0≤a*(b*c*d) := mul_nonneg ha (mul_nonneg (mul_nonneg hb hc) hd)
private theorem sign_nnp {a b c d : ℝ} (ha : 0≤a) (hb : b≤0) (hc : c≤0) (hd : 0≤d) :
    0≤a*(b*c*d) := mul_nonneg ha (mul_nonneg (mul_nonneg_of_nonpos_of_nonpos hb hc) hd)
private theorem sign_npn {a b c d : ℝ} (ha : 0≤a) (hb : b≤0) (hc : 0≤c) (hd : d≤0) :
    0≤a*(b*c*d) := mul_nonneg ha (mul_nonneg_of_nonpos_of_nonpos
      (mul_nonpos_of_nonpos_of_nonneg hb hc) hd)
private theorem sign_nnn {a b c d : ℝ} (ha : 0≤a) (hb : b≤0) (hc : c≤0) (hd : d≤0) :
    a*(b*c*d)≤0 := mul_nonpos_of_nonneg_of_nonpos ha
      (mul_nonpos_of_nonneg_of_nonpos (mul_nonneg_of_nonpos_of_nonpos hb hc) hd)
private theorem sign_npp {a b c d : ℝ} (ha : 0≤a) (hb : b≤0) (hc : 0≤c) (hd : 0≤d) :
    a*(b*c*d)≤0 := mul_nonpos_of_nonneg_of_nonpos ha
      (mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hb hc) hd)
private theorem sign_ppn {a b c d : ℝ} (ha : 0≤a) (hb : 0≤b) (hc : 0≤c) (hd : d≤0) :
    a*(b*c*d)≤0 := mul_nonpos_of_nonneg_of_nonpos ha
      (mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hb hc) hd)

theorem selected_triangle {n i j k : ℕ} (hn : 3≤n)
    (hij : i < j) (hjk : j < k) (hkn : k < n)
    (hs : LowBand n (i+j+k) ∨ HighBand n (i+j+k)) :
    TrianglePredicate n (arrangement n) ⟨i,j,k⟩ := by
  have hin : i < n := by omega
  have hjn : j < n := by omega
  refine ⟨hij,hjk,hkn,?_,?_⟩
  · dsimp [arrangement]
    rw [eval_line,angle_sum]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num)
      (ne_of_lt (sin_diff_neg hij hjn))) (ne_of_gt (sin_diff_pos hjk hkn)))
      (ne_of_gt (sin_diff_pos (by omega : i < k) hkn))) (selected_sum_nonzero hn hs)
  · intro r
    dsimp [arrangement]
    simp only [oriented_line]
    by_cases hri : r.val=i
    · rw [hri]
      simp only [sub_self,Real.sin_zero,mul_zero,zero_mul,le_refl,true_and]
      exact le_total 0 _
    by_cases hrj : r.val=j
    · rw [hrj]
      simp only [sub_self,Real.sin_zero,mul_zero,zero_mul,le_refl,true_and,and_true]
      exact le_total 0 _
    by_cases hrk : r.val=k
    · rw [hrk]
      simp only [sub_self,Real.sin_zero,mul_zero,zero_mul,le_refl,and_true]
      exact le_total 0 _
    simp only [angle_sum]
    rcases hs with hs | hs
    · have hsik : LowBand n (i+k+j) := by simpa [Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using hs
      have hsjk : LowBand n (j+k+i) := by simpa [Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using hs
      by_cases h1 : r.val < i
      · have si := sin_diff_neg h1 hin
        have sj := sin_diff_neg (show r.val < j by omega) hjn
        have sk := sin_diff_neg (show r.val < k by omega) hkn
        have s1 := low_before hn hs (show r.val < k by omega)
        have s2 := low_before hn hsik (show r.val < j by omega)
        have s3 := low_before hn hsjk h1
        left; exact ⟨sign_nnp (by positivity) sj.le si.le s1.le, sign_nnp (by positivity) sk.le si.le s2.le, sign_nnp (by positivity) sk.le sj.le s3.le⟩
      · by_cases h2 : r.val < j
        · have si := sin_diff_pos (show i < r.val by omega) r.isLt
          have sj := sin_diff_neg h2 hjn
          have sk := sin_diff_neg (show r.val < k by omega) hkn
          have s1 := low_before hn hs (show r.val < k by omega)
          have s2 := low_before hn hsik h2
          have s3 := low_after hn r.isLt hsjk (show i < r.val by omega)
          right
          exact ⟨sign_npp (by positivity) sj.le si.le s1.le, sign_npp (by positivity) sk.le si.le s2.le, sign_nnn (by positivity) sk.le sj.le s3.le⟩
        · by_cases h3 : r.val < k
          · have si := sin_diff_pos (show i < r.val by omega) r.isLt
            have sj := sin_diff_pos (show j < r.val by omega) r.isLt
            have sk := sin_diff_neg h3 hkn
            have s1 := low_before hn hs h3
            have s2 := low_after hn r.isLt hsik (show j < r.val by omega)
            have s3 := low_after hn r.isLt hsjk (show i < r.val by omega)
            left; exact ⟨sign_ppp (by positivity) sj.le si.le s1.le, sign_npn (by positivity) sk.le si.le s2.le, sign_npn (by positivity) sk.le sj.le s3.le⟩
          · have si := sin_diff_pos (show i < r.val by omega) r.isLt
            have sj := sin_diff_pos (show j < r.val by omega) r.isLt
            have sk := sin_diff_pos (show k < r.val by omega) r.isLt
            have s1 := low_after hn r.isLt hs (show k < r.val by omega)
            have s2 := low_after hn r.isLt hsik (show j < r.val by omega)
            have s3 := low_after hn r.isLt hsjk (show i < r.val by omega)
            right
            exact ⟨sign_ppn (by positivity) sj.le si.le s1.le, sign_ppn (by positivity) sk.le si.le s2.le, sign_ppn (by positivity) sk.le sj.le s3.le⟩
    · have hsik : HighBand n (i+k+j) := by simpa [Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using hs
      have hsjk : HighBand n (j+k+i) := by simpa [Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using hs
      by_cases h1 : r.val < i
      · have si := sin_diff_neg h1 hin
        have sj := sin_diff_neg (show r.val < j by omega) hjn
        have sk := sin_diff_neg (show r.val < k by omega) hkn
        have s1 := high_before hn hkn hs (show r.val < k by omega)
        have s2 := high_before hn hjn hsik (show r.val < j by omega)
        have s3 := high_before hn hin hsjk h1
        right
        exact ⟨sign_nnn (by positivity) sj.le si.le s1.le, sign_nnn (by positivity) sk.le si.le s2.le, sign_nnn (by positivity) sk.le sj.le s3.le⟩
      · by_cases h2 : r.val < j
        · have si := sin_diff_pos (show i < r.val by omega) r.isLt
          have sj := sin_diff_neg h2 hjn
          have sk := sin_diff_neg (show r.val < k by omega) hkn
          have s1 := high_before hn hkn hs (show r.val < k by omega)
          have s2 := high_before hn hjn hsik h2
          have s3 := high_after hn r.isLt hsjk (show i < r.val by omega)
          left; exact ⟨sign_npn (by positivity) sj.le si.le s1.le, sign_npn (by positivity) sk.le si.le s2.le, sign_nnp (by positivity) sk.le sj.le s3.le⟩
        · by_cases h3 : r.val < k
          · have si := sin_diff_pos (show i < r.val by omega) r.isLt
            have sj := sin_diff_pos (show j < r.val by omega) r.isLt
            have sk := sin_diff_neg h3 hkn
            have s1 := high_before hn hkn hs h3
            have s2 := high_after hn r.isLt hsik (show j < r.val by omega)
            have s3 := high_after hn r.isLt hsjk (show i < r.val by omega)
            right
            exact ⟨sign_ppn (by positivity) sj.le si.le s1.le, sign_npp (by positivity) sk.le si.le s2.le, sign_npp (by positivity) sk.le sj.le s3.le⟩
          · have si := sin_diff_pos (show i < r.val by omega) r.isLt
            have sj := sin_diff_pos (show j < r.val by omega) r.isLt
            have sk := sin_diff_pos (show k < r.val by omega) r.isLt
            have s1 := high_after hn r.isLt hs (show k < r.val by omega)
            have s2 := high_after hn r.isLt hsik (show j < r.val by omega)
            have s3 := high_after hn r.isLt hsjk (show i < r.val by omega)
            left; exact ⟨sign_ppp (by positivity) sj.le si.le s1.le, sign_ppp (by positivity) sk.le si.le s2.le, sign_ppp (by positivity) sk.le sj.le s3.le⟩

theorem selected_indices {n i j k : ℕ} (hn : 3≤n)
    (hij : i < j) (hjk : j < k) (hkn : k < n)
    (hmod : (i+j+k)%n=0 ∨ (i+j+k)%n=n-1) :
    LowBand n (i+j+k) ∨ HighBand n (i+j+k) := by
  have hpos : 0<n := by omega
  have hmax : i+j+k < 3*n := by omega
  have hq : (i+j+k)/n < 3 := (Nat.div_lt_iff_lt_mul hpos).mpr (by omega)
  have he := Nat.mod_add_div (i+j+k) n
  have cases3 (q : ℕ) (hq : q < 3) : q=0 ∨ q=1 ∨ q=2 := by omega
  have hcases := cases3 _ hq
  unfold LowBand HighBand
  rcases hcases with hc | hc | hc <;> rw [hc] at he <;> norm_num at he <;> omega

theorem noConcurrent (n : ℕ) : NoConcurrent n (arrangement n) := by
  intro i j k hij hjk
  have hn : 3≤n := by have := k.isLt; omega
  have hs : Real.sin (sumAngle n (i.val+j.val+k.val))≠0 := by
    by_cases h0 : i.val+j.val+k.val+1≤n
    · exact (sum_sin_pos0 (by omega) h0).ne'
    by_cases h1 : i.val+j.val+k.val+1≤2*n
    · exact (sum_sin_neg1 (by omega) (by omega) h1).ne
    · exact (sum_sin_pos2 (by omega) (by omega) (by have := k.isLt; omega)).ne'
  dsimp only [arrangement]
  rw [eval_line,angle_sum]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num)
    (sin_diff_neg hij j.isLt).ne) (sin_diff_pos hjk k.isLt).ne')
    (sin_diff_pos (by omega : i.val<k.val) k.isLt).ne') hs

def lower (n : ℕ) : ℕ := n*(n-3)/3+1

theorem simple_lower_bound (n : ℕ) (hn : 3≤n) : SimpleLowerBound n (lower n) := by
  classical
  letI : NeZero n := ⟨by omega⟩
  let a : ZMod n := 0
  let b : ZMod n := ((n-1:ℕ):ZMod n)
  have hav : a.val=0 := by simp [a]
  have hbv : b.val=n-1 := ZMod.val_natCast_of_lt (by omega)
  have hab : a≠b := by
    intro h
    have hv := congrArg ZMod.val h
    rw [hav,hbv] at hv
    omega
  let os := FurediPalastiCount.ordered n a b
  let convert : FurediPalastiCount.Triple n → Triple :=
    fun p => ⟨p.1.val,p.2.1.val,p.2.2.val⟩
  have hi : Function.Injective convert := by
    rintro ⟨i,j,k⟩ ⟨i',j',k'⟩ h
    have h1 := congrArg Triple.i h
    have h2 := congrArg Triple.j h
    have h3 := congrArg Triple.k h
    dsimp [convert] at h1 h2 h3
    have e1 := ZMod.val_injective n h1
    have e2 := ZMod.val_injective n h2
    have e3 := ZMod.val_injective n h3
    simp [e1,e2,e3]
  refine ⟨arrangement n,noParallel n,noConcurrent n,os.toList.map convert,?_,?_,?_⟩
  · exact os.nodup_toList.map hi
  · intro t ht
    rcases List.mem_map.mp ht with ⟨p,hp,rfl⟩
    have hop := (FurediPalastiCount.mem_ordered n a b p).mp (Finset.mem_toList.mp hp)
    apply selected_triangle hn hop.2.1 hop.2.2 (ZMod.val_lt p.2.2)
    apply selected_indices hn hop.2.1 hop.2.2 (ZMod.val_lt p.2.2)
    have hcast : ((p.1.val+p.2.1.val+p.2.2.val : ℕ):ZMod n)=FurediPalastiCount.sum n p := by
      simp [FurediPalastiCount.sum]
    rcases hop.1 with ha | hb
    · left
      have he := congrArg ZMod.val (hcast.trans ha)
      simpa only [ZMod.val_natCast,hav] using he
    · right
      have he := congrArg ZMod.val (hcast.trans hb)
      simpa only [ZMod.val_natCast,hbv] using he
  · simpa only [List.length_map,Finset.length_toList,lower,os] using
      ShiftedCount.ordered_bound_plus n hn b hab

theorem lower_bound (n : ℕ) (hn : 3≤n) : LowerBound n (lower n) :=
  (simple_lower_bound n hn).classical

#print axioms simple_lower_bound
#print axioms lower_bound
end Kobon.ShiftedFurediPalasti
