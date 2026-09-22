import Kobon.FurediPalastiCaps
import Kobon.FurediPalastiWrap

/-! Two additional triangles from the leftmost pair of exposed vertices. -/
namespace Kobon.FurediPalastiTwoCaps
open FurediPalasti FurediPalastiChart FurediPalastiCaps

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
private theorem sign_ppn {a b c d : ℝ} (ha : 0≤a) (hb : 0≤b) (hc : 0≤c) (hd : d≤0) :
    a*(b*c*d)≤0 := mul_nonpos_of_nonneg_of_nonpos ha
      (mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hb hc) hd)

theorem upper_cap_sign (k r : ℕ) (hk : 1≤k) (hr : r<6*k+3) :
    if r<2*k+1 then
      0≤orientedEval (arrangement (6*k+3) r) (arrangement (6*k+3) (2*k))
        (arrangement (6*k+3) (2*k+1))
    else orientedEval (arrangement (6*k+3) r) (arrangement (6*k+3) (2*k))
        (arrangement (6*k+3) (2*k+1))≤0 := by
  by_cases h0 : r=2*k
  · subst r; simp [arrangement,oriented_line]
  by_cases h1 : r=2*k+1
  · subst r; simp [arrangement,oriented_line]
  dsimp only [arrangement]
  rw [oriented_line,angle_sum]
  by_cases hregion : r<2*k+1
  · rw [if_pos hregion]
    exact sign_nnp (by positivity)
      (sin_diff_neg hregion (by omega)).le
      (sin_diff_neg (by omega : r<2*k) (by omega)).le
      (sum_sin_pos0 (n:=6*k+3) (s:=2*k+(2*k+1)+r) (by omega) (by omega)).le
  · rw [if_neg hregion]
    exact sign_ppn (by positivity)
      (sin_diff_pos (by omega : 2*k+1<r) hr).le
      (sin_diff_pos (by omega : 2*k<r) hr).le
      (sum_sin_neg1 (n:=6*k+3) (s:=2*k+(2*k+1)+r) (by omega) (by omega) (by omega)).le

theorem upper_outer_sign (k r : ℕ) (hk : 1≤k) (hr : r<6*k+3) :
    if r<2*k+1 then
      orientedEval (arrangement (6*k+3) r) (arrangement (6*k+3) (2*k))
        (arrangement (6*k+3) (5*k+2))≤0
    else 0≤orientedEval (arrangement (6*k+3) r) (arrangement (6*k+3) (2*k))
        (arrangement (6*k+3) (5*k+2)) := by
  by_cases h0 : r=2*k
  · subst r; simp [arrangement,oriented_line]
  by_cases h1 : r=5*k+2
  · subst r; simp [arrangement,oriented_line]
  dsimp only [arrangement]
  rw [oriented_line,angle_sum]
  by_cases hregion : r<2*k+1
  · rw [if_pos hregion]
    exact sign_nnn (by positivity)
      (sin_diff_neg (by omega : r<5*k+2) (by omega)).le
      (sin_diff_neg (by omega : r<2*k) (by omega)).le
      (sum_sin_neg1 (n:=6*k+3) (s:=2*k+(5*k+2)+r) (by omega) (by omega) (by omega)).le
  · rw [if_neg hregion]
    have s2 := (sin_diff_pos (by omega : 2*k<r) hr).le
    by_cases hlast : r<5*k+2
    · exact sign_npn (by positivity) (sin_diff_neg hlast (by omega)).le s2
        (sum_sin_neg1 (n:=6*k+3) (s:=2*k+(5*k+2)+r) (by omega) (by omega) (by omega)).le
    · exact sign_ppp (by positivity) (sin_diff_pos (by omega : 5*k+2<r) hr).le s2
        (sum_sin_pos2 (n:=6*k+3) (s:=2*k+(5*k+2)+r) (by omega) (by omega) (by omega)).le

theorem upper_inner_sign (k r : ℕ) (hk : 1≤k) (hr : r<6*k+3) :
    if r<2*k+1 then
      orientedEval (arrangement (6*k+3) r) (arrangement (6*k+3) (2*k+1))
        (arrangement (6*k+3) (5*k+2))≤0
    else 0≤orientedEval (arrangement (6*k+3) r) (arrangement (6*k+3) (2*k+1))
        (arrangement (6*k+3) (5*k+2)) := by
  by_cases h0 : r=2*k+1
  · subst r; simp [arrangement,oriented_line]
  by_cases h1 : r=5*k+2
  · subst r; simp [arrangement,oriented_line]
  dsimp only [arrangement]
  rw [oriented_line,angle_sum]
  by_cases hregion : r<2*k+1
  · rw [if_pos hregion]
    exact sign_nnn (by positivity)
      (sin_diff_neg (by omega : r<5*k+2) (by omega)).le
      (sin_diff_neg hregion (by omega)).le
      (sum_sin_neg1 (n:=6*k+3) (s:=(2*k+1)+(5*k+2)+r) (by omega) (by omega) (by omega)).le
  · rw [if_neg hregion]
    have s2 := (sin_diff_pos (by omega : 2*k+1<r) hr).le
    by_cases hlast : r<5*k+2
    · exact sign_npn (by positivity) (sin_diff_neg hlast (by omega)).le s2
        (sum_sin_neg1 (n:=6*k+3) (s:=(2*k+1)+(5*k+2)+r) (by omega) (by omega) (by omega)).le
    · exact sign_ppp (by positivity) (sin_diff_pos (by omega : 5*k+2<r) hr).le s2
        (sum_sin_pos2 (n:=6*k+3) (s:=(2*k+1)+(5*k+2)+r) (by omega) (by omega) (by omega)).le

theorem upper_triangle (k : ℕ) (hk : 1≤k) (h : ℝ) (hh : h<0)
    (hcap : -cap (6*k+3)/2<h)
    (hcut : ∀ i j : Fin (6*k+3), i<j → ¬ LeftCaps (2*k+1) i j →
      h<(intersection (arrangement (6*k+3) i) (arrangement (6*k+3) j)).1) :
    TrianglePredicate (6*k+3)
      (fun i => Projective.transform h (arrangement (6*k+3) i)) ⟨2*k,2*k+1,5*k+2⟩ := by
  have hn : 3*(2*k+1)=6*k+3 := by omega
  have d1 := noParallel (6*k+3) ⟨2*k,by omega⟩ ⟨2*k+1,by omega⟩ (by change 2*k<2*k+1; omega)
  have d2 := noParallel (6*k+3) ⟨2*k,by omega⟩ ⟨5*k+2,by omega⟩ (by change 2*k<5*k+2; omega)
  have d3 := noParallel (6*k+3) ⟨2*k+1,by omega⟩ ⟨5*k+2,by omega⟩ (by change 2*k+1<5*k+2; omega)
  have c1 : (intersection (arrangement (6*k+3) (2*k)) (arrangement (6*k+3) (2*k+1))).1<h := by
    have hv := left_cap_value (m:=2*k+1) (i:=2*k) (j:=2*k+1)
      (by omega) (by omega) (by omega) (Or.inl ⟨rfl,rfl⟩)
    rw [hn] at hv
    rw [hv]; exact hcap
  have c2 : h<(intersection (arrangement (6*k+3) (2*k)) (arrangement (6*k+3) (5*k+2))).1 :=
    hcut ⟨2*k,by omega⟩ ⟨5*k+2,by omega⟩ (by change 2*k<5*k+2; omega)
      (by dsimp [LeftCaps]; omega)
  have c3 : h<(intersection (arrangement (6*k+3) (2*k+1)) (arrangement (6*k+3) (5*k+2))).1 :=
    hcut ⟨2*k+1,by omega⟩ ⟨5*k+2,by omega⟩ (by change 2*k+1<5*k+2; omega)
      (by dsimp [LeftCaps]; omega)
  refine ⟨by dsimp; omega,by dsimp; omega,by dsimp; omega,?_,?_⟩
  · rw [Projective.eval_transform]
    exact mul_ne_zero (pow_ne_zero _ hh.ne)
      (FurediPalastiWrap.halfphase_simple (6*k+3) ⟨2*k,by omega⟩ ⟨2*k+1,by omega⟩
        ⟨5*k+2,by omega⟩ (by change 2*k<2*k+1; omega) (by change 2*k+1<5*k+2; omega))
  · intro r
    have s1 := upper_cap_sign k r hk r.isLt
    have s2 := upper_outer_sign k r hk r.isLt
    have s3 := upper_inner_sign k r hk r.isLt
    by_cases hr : r.val<2*k+1
    · simp only [if_pos hr] at s1 s2 s3
      right
      exact ⟨Projective.nonneg_flipped_negative h _ _ _ hh d1 c1 s1,
        Projective.nonpos_preserved_negative h _ _ _ hh d2 c2 s2,
        Projective.nonpos_preserved_negative h _ _ _ hh d3 c3 s3⟩
    · simp only [if_neg hr] at s1 s2 s3
      left
      exact ⟨Projective.nonpos_flipped_negative h _ _ _ hh d1 c1 s1,
        Projective.nonneg_preserved_negative h _ _ _ hh d2 c2 s2,
        Projective.nonneg_preserved_negative h _ _ _ hh d3 c3 s3⟩

theorem lower_cap_sign (k r : ℕ) (hk : 1≤k) (hr : r<6*k+3) :
    if r<4*k+2 then
      orientedEval (arrangement (6*k+3) r) (arrangement (6*k+3) (4*k+1))
        (arrangement (6*k+3) (4*k+2))≤0
    else 0≤orientedEval (arrangement (6*k+3) r) (arrangement (6*k+3) (4*k+1))
        (arrangement (6*k+3) (4*k+2)) := by
  by_cases h0 : r=4*k+1
  · subst r; simp [arrangement,oriented_line]
  by_cases h1 : r=4*k+2
  · subst r; simp [arrangement,oriented_line]
  dsimp only [arrangement]
  rw [oriented_line,angle_sum]
  by_cases hregion : r<4*k+2
  · rw [if_pos hregion]
    exact sign_nnn (by positivity)
      (sin_diff_neg hregion (by omega)).le
      (sin_diff_neg (by omega : r<4*k+1) (by omega)).le
      (sum_sin_neg1 (n:=6*k+3) (s:=(4*k+1)+(4*k+2)+r) (by omega) (by omega) (by omega)).le
  · rw [if_neg hregion]
    exact sign_ppp (by positivity)
      (sin_diff_pos (by omega : 4*k+2<r) hr).le
      (sin_diff_pos (by omega : 4*k+1<r) hr).le
      (sum_sin_pos2 (n:=6*k+3) (s:=(4*k+1)+(4*k+2)+r) (by omega) (by omega) (by omega)).le

theorem lower_outer_sign (k r : ℕ) (hk : 1≤k) (hr : r<6*k+3) :
    if r<4*k+2 then
      0≤orientedEval (arrangement (6*k+3) r) (arrangement (6*k+3) k)
        (arrangement (6*k+3) (4*k+2))
    else orientedEval (arrangement (6*k+3) r) (arrangement (6*k+3) k)
        (arrangement (6*k+3) (4*k+2))≤0 := by
  by_cases h0 : r=k
  · subst r; simp [arrangement,oriented_line]
  by_cases h1 : r=4*k+2
  · subst r; simp [arrangement,oriented_line]
  dsimp only [arrangement]
  rw [oriented_line,angle_sum]
  by_cases hregion : r<4*k+2
  · rw [if_pos hregion]
    have s1 := (sin_diff_neg (n:=6*k+3) hregion (by omega)).le
    by_cases hlow : r<k
    · exact sign_nnp (by positivity) s1 (sin_diff_neg hlow (by omega)).le
        (sum_sin_pos0 (n:=6*k+3) (s:=k+(4*k+2)+r) (by omega) (by omega)).le
    · exact sign_npn (by positivity) s1 (sin_diff_pos (by omega : k<r) hr).le
        (sum_sin_neg1 (n:=6*k+3) (s:=k+(4*k+2)+r) (by omega) (by omega) (by omega)).le
  · rw [if_neg hregion]
    exact sign_ppn (by positivity)
      (sin_diff_pos (by omega : 4*k+2<r) hr).le
      (sin_diff_pos (by omega : k<r) hr).le
      (sum_sin_neg1 (n:=6*k+3) (s:=k+(4*k+2)+r) (by omega) (by omega) (by omega)).le

theorem lower_inner_sign (k r : ℕ) (hk : 1≤k) (hr : r<6*k+3) :
    if r<4*k+2 then
      0≤orientedEval (arrangement (6*k+3) r) (arrangement (6*k+3) k)
        (arrangement (6*k+3) (4*k+1))
    else orientedEval (arrangement (6*k+3) r) (arrangement (6*k+3) k)
        (arrangement (6*k+3) (4*k+1))≤0 := by
  by_cases h0 : r=k
  · subst r; simp [arrangement,oriented_line]
  by_cases h1 : r=4*k+1
  · subst r; simp [arrangement,oriented_line]
  dsimp only [arrangement]
  rw [oriented_line,angle_sum]
  by_cases hregion : r<4*k+2
  · rw [if_pos hregion]
    have s1 := (sin_diff_neg (n:=6*k+3) (by omega : r<4*k+1) (by omega)).le
    by_cases hlow : r<k
    · exact sign_nnp (by positivity) s1 (sin_diff_neg hlow (by omega)).le
        (sum_sin_pos0 (n:=6*k+3) (s:=k+(4*k+1)+r) (by omega) (by omega)).le
    · exact sign_npn (by positivity) s1 (sin_diff_pos (by omega : k<r) hr).le
        (sum_sin_neg1 (n:=6*k+3) (s:=k+(4*k+1)+r) (by omega) (by omega) (by omega)).le
  · rw [if_neg hregion]
    exact sign_ppn (by positivity)
      (sin_diff_pos (by omega : 4*k+1<r) hr).le
      (sin_diff_pos (by omega : k<r) hr).le
      (sum_sin_neg1 (n:=6*k+3) (s:=k+(4*k+1)+r) (by omega) (by omega) (by omega)).le

theorem lower_triangle (k : ℕ) (hk : 1≤k) (h : ℝ) (hh : h<0)
    (hcap : -cap (6*k+3)/2<h)
    (hcut : ∀ i j : Fin (6*k+3), i<j → ¬ LeftCaps (2*k+1) i j →
      h<(intersection (arrangement (6*k+3) i) (arrangement (6*k+3) j)).1) :
    TrianglePredicate (6*k+3)
      (fun i => Projective.transform h (arrangement (6*k+3) i)) ⟨k,4*k+1,4*k+2⟩ := by
  have hn : 3*(2*k+1)=6*k+3 := by omega
  have d1 := noParallel (6*k+3) ⟨k,by omega⟩ ⟨4*k+1,by omega⟩ (by change k<4*k+1; omega)
  have d2 := noParallel (6*k+3) ⟨k,by omega⟩ ⟨4*k+2,by omega⟩ (by change k<4*k+2; omega)
  have d3 := noParallel (6*k+3) ⟨4*k+1,by omega⟩ ⟨4*k+2,by omega⟩ (by change 4*k+1<4*k+2; omega)
  have c3 : (intersection (arrangement (6*k+3) (4*k+1)) (arrangement (6*k+3) (4*k+2))).1<h := by
    have hv := left_cap_value (m:=2*k+1) (i:=4*k+1) (j:=4*k+2)
      (by omega) (by omega) (by omega) (Or.inr ⟨by omega,by omega⟩)
    rw [hn] at hv
    rw [hv]; exact hcap
  have c1 : h<(intersection (arrangement (6*k+3) k) (arrangement (6*k+3) (4*k+1))).1 :=
    hcut ⟨k,by omega⟩ ⟨4*k+1,by omega⟩ (by change k<4*k+1; omega)
      (by dsimp [LeftCaps]; omega)
  have c2 : h<(intersection (arrangement (6*k+3) k) (arrangement (6*k+3) (4*k+2))).1 :=
    hcut ⟨k,by omega⟩ ⟨4*k+2,by omega⟩ (by change k<4*k+2; omega)
      (by dsimp [LeftCaps]; omega)
  refine ⟨by dsimp; omega,by dsimp; omega,by dsimp; omega,?_,?_⟩
  · rw [Projective.eval_transform]
    exact mul_ne_zero (pow_ne_zero _ hh.ne)
      (FurediPalastiWrap.halfphase_simple (6*k+3) ⟨k,by omega⟩ ⟨4*k+1,by omega⟩
        ⟨4*k+2,by omega⟩ (by change k<4*k+1; omega) (by change 4*k+1<4*k+2; omega))
  · intro r
    have s1 := lower_inner_sign k r hk r.isLt
    have s2 := lower_outer_sign k r hk r.isLt
    have s3 := lower_cap_sign k r hk r.isLt
    by_cases hr : r.val<4*k+2
    · simp only [if_pos hr] at s1 s2 s3
      left
      exact ⟨Projective.nonneg_preserved_negative h _ _ _ hh d1 c1 s1,
        Projective.nonneg_preserved_negative h _ _ _ hh d2 c2 s2,
        Projective.nonpos_flipped_negative h _ _ _ hh d3 c3 s3⟩
    · simp only [if_neg hr] at s1 s2 s3
      right
      exact ⟨Projective.nonpos_preserved_negative h _ _ _ hh d1 c1 s1,
        Projective.nonpos_preserved_negative h _ _ _ hh d2 c2 s2,
        Projective.nonneg_flipped_negative h _ _ _ hh d3 c3 s3⟩

theorem selected_preserved (k : ℕ) (hk : 1≤k) (h : ℝ) (hh : h<0)
    (hcut : ∀ i j : Fin (6*k+3), i<j → ¬ LeftCaps (2*k+1) i j →
      h<(intersection (arrangement (6*k+3) i) (arrangement (6*k+3) j)).1)
    (i j l : ℕ) (hij : i<j) (hjl : j<l) (hln : l<6*k+3)
    (hs : LowBand (6*k+3) (i+j+l) ∨ HighBand (6*k+3) (i+j+l)) :
    TrianglePredicate (6*k+3)
      (fun i => Projective.transform h (arrangement (6*k+3) i)) ⟨i,j,l⟩ := by
  have hi : i<6*k+3 := by omega
  have hj : j<6*k+3 := by omega
  apply Projective.triangle_preserved_negative (6*k+3) (arrangement (6*k+3)) h hh
    (noParallel (6*k+3)) ⟨i,j,l⟩ (selected_triangle (by omega) hij hjl hln hs)
  · apply hcut ⟨i,hi⟩ ⟨j,hj⟩ hij
    dsimp [LeftCaps]
    unfold LowBand HighBand at hs
    omega
  · apply hcut ⟨i,hi⟩ ⟨l,hln⟩ (by change i<l; omega)
    dsimp [LeftCaps]
    unfold LowBand HighBand at hs
    omega
  · apply hcut ⟨j,hj⟩ ⟨l,hln⟩ hjl
    dsimp [LeftCaps]
    unfold LowBand HighBand at hs
    omega

theorem two_cap_simple_lower_bound (k : ℕ) (hk : 1≤k) :
    SimpleLowerBound (6*k+3) (FurediPalasti.lower (6*k+3)+2) := by
  classical
  have hne : 3*(2*k+1)=6*k+3 := by omega
  have hex := exists_left_cut (2*k+1) (by omega)
  rw [hne] at hex
  rcases hex with ⟨h,hh,hcap,hcut⟩
  let L := fun i => Projective.transform h (arrangement (6*k+3) i)
  have hp : NoParallel (6*k+3) L := by
    apply Projective.noParallel_transform (6*k+3) (arrangement (6*k+3)) h hh.ne (noParallel (6*k+3))
    intro i j hij
    by_cases he : LeftCaps (2*k+1) i j
    · have hv := left_cap_value (m:=2*k+1) (i:=i) (j:=j) (by omega) hij
        (by rw [hne]; exact j.isLt) he
      rw [hne] at hv
      rw [hv]
      exact hcap.ne
    · exact (hcut i j hij he).ne'
  have hsimple : NoConcurrent (6*k+3) L := by
    intro i j l hij hjl
    dsimp [L]
    rw [Projective.eval_transform]
    exact mul_ne_zero (pow_ne_zero _ hh.ne)
      (FurediPalastiWrap.halfphase_simple (6*k+3) i j l hij hjl)
  rcases FurediPalastiWrap.selected_witness (6*k+3) (by omega) with
    ⟨ts,hts,hselected,hcount⟩
  let upper : Triple := ⟨2*k,2*k+1,5*k+2⟩
  let lower : Triple := ⟨k,4*k+1,4*k+2⟩
  have hu : upper∉ts := by
    intro ht
    have hs := (hselected upper ht).2.2.2
    dsimp [upper] at hs
    unfold LowBand HighBand at hs
    omega
  have hl : lower∉ts := by
    intro ht
    have hs := (hselected lower ht).2.2.2
    dsimp [lower] at hs
    unfold LowBand HighBand at hs
    omega
  have hul : upper≠lower := by
    intro he
    have hv := congrArg Triple.i he
    dsimp [upper,lower] at hv
    omega
  have hut : TrianglePredicate (6*k+3) L upper := upper_triangle k hk h hh hcap hcut
  have hlt : TrianglePredicate (6*k+3) L lower := lower_triangle k hk h hh hcap hcut
  refine ⟨L,hp,hsimple,upper::lower::ts,?_,?_,?_⟩
  · exact List.nodup_cons.mpr ⟨by simpa only [List.mem_cons,not_or] using And.intro hul hu,
      List.nodup_cons.mpr ⟨hl,hts⟩⟩
  · intro t ht
    rcases List.mem_cons.mp ht with ht | ht
    · simpa only [ht] using hut
    rcases List.mem_cons.mp ht with ht | ht
    · simpa only [ht] using hlt
    rcases hselected t ht with ⟨h1,h2,h3,hs⟩
    exact selected_preserved k hk h hh hcut t.i t.j t.k h1 h2 h3 hs
  · simpa only [List.length_cons] using Nat.add_le_add_right hcount 2

theorem two_cap_lower_bound (k : ℕ) (hk : 1≤k) :
    LowerBound (6*k+3) (FurediPalasti.lower (6*k+3)+2) :=
  (two_cap_simple_lower_bound k hk).classical

#print axioms upper_triangle
#print axioms lower_triangle
#print axioms two_cap_simple_lower_bound

end Kobon.FurediPalastiTwoCaps
