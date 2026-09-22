import Kobon.FurediPalastiChart

/-! The additional triangle obtained by moving infinity beyond the unique
rightmost vertex of an odd classical arrangement. -/
namespace Kobon.FurediPalastiWrap
open FurediPalasti FurediPalastiChart

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

theorem cap_nonneg (m r : ℕ) (hm : 1≤m) (hr : r<2*m+1) :
    0≤orientedEval (arrangement (2*m+1) r)
      (arrangement (2*m+1) 0) (arrangement (2*m+1) (2*m)) := by
  dsimp only [arrangement]
  rw [oriented_line]
  by_cases h0 : r=0
  · simp [h0]
  by_cases hlast : r=2*m
  · simp [hlast]
  rw [angle_sum]
  have s1 := sin_diff_neg (by omega : r<2*m) (by omega : 2*m<2*m+1)
  have s2 := sin_diff_pos (by omega : 0<r) hr
  have s3 := sum_sin_neg1 (n:=2*m+1) (s:=0+2*m+r) (by omega) (by omega) (by omega)
  exact sign_npn (by positivity) s1.le s2.le s3.le

theorem lower_pair_nonpos (m r : ℕ) (hm : 1≤m) (hr : r<2*m+1) :
    orientedEval (arrangement (2*m+1) r)
      (arrangement (2*m+1) 0) (arrangement (2*m+1) m)≤0 := by
  dsimp only [arrangement]
  rw [oriented_line]
  by_cases h0 : r=0
  · simp [h0]
  by_cases hmid : r=m
  · simp [hmid]
  rw [angle_sum]
  have s2 := sin_diff_pos (by omega : 0<r) hr
  by_cases hlt : r<m
  · have s1 := sin_diff_neg hlt (by omega : m<2*m+1)
    have s3 := sum_sin_pos0 (n:=2*m+1) (s:=0+m+r) (by omega) (by omega)
    exact sign_npp (by positivity) s1.le s2.le s3.le
  · have s1 := sin_diff_pos (by omega : m<r) hr
    have s3 := sum_sin_neg1 (n:=2*m+1) (s:=0+m+r) (by omega) (by omega) (by omega)
    exact sign_ppn (by positivity) s1.le s2.le s3.le

theorem upper_pair_nonpos (m r : ℕ) (hm : 1≤m) (hr : r<2*m+1) :
    orientedEval (arrangement (2*m+1) r)
      (arrangement (2*m+1) m) (arrangement (2*m+1) (2*m))≤0 := by
  dsimp only [arrangement]
  rw [oriented_line]
  by_cases hmid : r=m
  · simp [hmid]
  by_cases hlast : r=2*m
  · simp [hlast]
  rw [angle_sum]
  have s1 := sin_diff_neg (by omega : r<2*m) (by omega : 2*m<2*m+1)
  by_cases hlt : r<m
  · have s2 := sin_diff_neg hlt (by omega : m<2*m+1)
    have s3 := sum_sin_neg1 (n:=2*m+1) (s:=m+2*m+r) (by omega) (by omega) (by omega)
    exact sign_nnn (by positivity) s1.le s2.le s3.le
  · have s2 := sin_diff_pos (by omega : m<r) hr
    have s3 := sum_sin_pos2 (n:=2*m+1) (s:=m+2*m+r) (by omega) (by omega) (by omega)
    exact sign_npp (by positivity) s1.le s2.le s3.le

theorem wrap_triangle (m : ℕ) (hm : 1≤m) (h : ℝ) (hh : 0<h)
    (hcap : h<cap (2*m+1))
    (hcut : ∀ i j : Fin (2*m+1), i<j → (i.val≠0 ∨ j.val≠2*m) →
      (intersection (arrangement (2*m+1) i) (arrangement (2*m+1) j)).1<h) :
    TrianglePredicate (2*m+1)
      (fun i => Projective.transform h (arrangement (2*m+1) i)) ⟨0,m,2*m⟩ := by
  have d1 : det (arrangement (2*m+1) 0) (arrangement (2*m+1) m)≠0 :=
    noParallel (2*m+1) ⟨0,by omega⟩ ⟨m,by omega⟩ (by change 0<m; omega)
  have d2 : det (arrangement (2*m+1) 0) (arrangement (2*m+1) (2*m))≠0 :=
    noParallel (2*m+1) ⟨0,by omega⟩ ⟨2*m,by omega⟩ (by change 0<2*m; omega)
  have d3 : det (arrangement (2*m+1) m) (arrangement (2*m+1) (2*m))≠0 :=
    noParallel (2*m+1) ⟨m,by omega⟩ ⟨2*m,by omega⟩ (by change m<2*m; omega)
  have c1 : (intersection (arrangement (2*m+1) 0) (arrangement (2*m+1) m)).1<h :=
    hcut ⟨0,by omega⟩ ⟨m,by omega⟩ (by change 0<m; omega) (by right; dsimp; omega)
  have c3 : (intersection (arrangement (2*m+1) m) (arrangement (2*m+1) (2*m))).1<h :=
    hcut ⟨m,by omega⟩ ⟨2*m,by omega⟩ (by change m<2*m; omega) (by left; dsimp; omega)
  have c2 : h<(intersection (arrangement (2*m+1) 0) (arrangement (2*m+1) (2*m))).1 := by
    have hv := cap_vertex (2*m+1) (by omega)
    have he : 2*m+1-1=2*m := by omega
    rw [he] at hv
    rw [hv]
    exact hcap
  refine ⟨by dsimp; omega,by dsimp; omega,by dsimp; omega,?_,?_⟩
  · rw [Projective.eval_transform]
    apply mul_ne_zero (pow_ne_zero _ hh.ne')
    dsimp only [arrangement]
    rw [eval_line,angle_sum]
    have s1 := sin_diff_neg (by omega : 0<m) (by omega : m<2*m+1)
    have s2 := sin_diff_pos (by omega : m<2*m) (by omega : 2*m<2*m+1)
    have s3 := sin_diff_pos (by omega : 0<2*m) (by omega : 2*m<2*m+1)
    have s4 := sum_sin_neg1 (n:=2*m+1) (s:=0+m+2*m) (by omega) (by omega) (by omega)
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) s1.ne) s2.ne') s3.ne') s4.ne
  · intro r
    right
    exact ⟨Projective.nonpos_preserved h _ _ _ hh d1 c1 (lower_pair_nonpos m r hm r.isLt),
      Projective.nonneg_flipped h _ _ _ hh d2 c2 (cap_nonneg m r hm r.isLt),
      Projective.nonpos_preserved h _ _ _ hh d3 c3 (upper_pair_nonpos m r hm r.isLt)⟩

theorem selected_preserved (n : ℕ) (hn : 3≤n) (h : ℝ) (hh : 0<h)
    (hcut : ∀ i j : Fin n, i<j → (i.val≠0 ∨ j.val≠n-1) →
      (intersection (arrangement n i) (arrangement n j)).1<h)
    (i j k : ℕ) (hij : i<j) (hjk : j<k) (hkn : k<n)
    (hs : LowBand n (i+j+k) ∨ HighBand n (i+j+k)) :
    TrianglePredicate n (fun i => Projective.transform h (arrangement n i)) ⟨i,j,k⟩ := by
  have hi : i<n := by omega
  have hj : j<n := by omega
  apply Projective.triangle_preserved n (arrangement n) h hh (noParallel n) ⟨i,j,k⟩
    (selected_triangle hn hij hjk hkn hs)
  · exact hcut ⟨i,hi⟩ ⟨j,hj⟩ hij (by right; dsimp; omega)
  · apply hcut ⟨i,hi⟩ ⟨k,hkn⟩ (by change i<k; omega)
    dsimp
    unfold LowBand HighBand at hs
    omega
  · exact hcut ⟨j,hj⟩ ⟨k,hkn⟩ hjk (by left; dsimp; omega)

theorem selected_witness (n : ℕ) (hn : 3≤n) :
    ∃ ts : List Triple, ts.Nodup ∧
      (∀ t ∈ ts, t.i<t.j ∧ t.j<t.k ∧ t.k<n ∧
        (LowBand n (t.i+t.j+t.k) ∨ HighBand n (t.i+t.j+t.k))) ∧
      FurediPalasti.lower n≤ts.length := by
  classical
  letI : NeZero n := ⟨by omega⟩
  let a : ZMod n := ((n-1:ℕ):ZMod n)
  let b : ZMod n := ((n-2:ℕ):ZMod n)
  have hav : a.val=n-1 := ZMod.val_natCast_of_lt (by omega)
  have hbv : b.val=n-2 := ZMod.val_natCast_of_lt (by omega)
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
  refine ⟨os.toList.map convert,os.nodup_toList.map hi,?_,?_⟩
  · intro t ht
    rcases List.mem_map.mp ht with ⟨p,hp,rfl⟩
    have hop := (FurediPalastiCount.mem_ordered n a b p).mp (Finset.mem_toList.mp hp)
    refine ⟨hop.2.1,hop.2.2,ZMod.val_lt p.2.2,?_⟩
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
  · simpa only [List.length_map,Finset.length_toList,FurediPalasti.lower,os] using
      FurediPalastiCount.ordered_bound n hn a b hab

theorem halfphase_simple (n : ℕ) : NoConcurrent n (arrangement n) := by
  intro i j k hij hjk
  have hn : 3≤n := by have := k.isLt; omega
  have hs : Real.sin (sumAngle n (i.val+j.val+k.val))≠0 := by
    by_cases h0 : i.val+j.val+k.val+2≤n
    · exact (sum_sin_pos0 (by omega) h0).ne'
    by_cases h1 : i.val+j.val+k.val+2≤2*n
    · exact (sum_sin_neg1 (by omega) (by omega) h1).ne
    · exact (sum_sin_pos2 (by omega) (by omega) (by have := k.isLt; omega)).ne'
  dsimp only [arrangement]
  rw [eval_line,angle_sum]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num)
    (sin_diff_neg hij j.isLt).ne) (sin_diff_pos hjk k.isLt).ne')
    (sin_diff_pos (by omega : i.val<k.val) k.isLt).ne') hs

theorem one_cap_simple_lower_bound (m : ℕ) (hm : 1≤m) :
    SimpleLowerBound (2*m+1) (FurediPalasti.lower (2*m+1)+1) := by
  classical
  let n := 2*m+1
  have hn : 3≤n := by dsimp [n]; omega
  rcases exists_cut n hn with ⟨h,hh,hcap,hcut⟩
  let L := fun i => Projective.transform h (arrangement n i)
  have hp : NoParallel n L := by
    apply Projective.noParallel_transform n (arrangement n) h hh.ne' (noParallel n)
    intro i j hij
    by_cases he : i.val=0 ∧ j.val=n-1
    · rcases he with ⟨he1,he2⟩
      rw [he1,he2,cap_vertex n (by omega)]
      exact (ne_of_lt hcap).symm
    · have hne : i.val≠0 ∨ j.val≠n-1 := by tauto
      exact (hcut i j hij hne).ne
  have hsimple : NoConcurrent n L := by
    intro i j k hij hjk
    dsimp [L]
    rw [Projective.eval_transform]
    exact mul_ne_zero (pow_ne_zero _ hh.ne') (halfphase_simple n i j k hij hjk)
  rcases selected_witness n hn with ⟨ts,hts,hselected,hcount⟩
  let extra : Triple := ⟨0,m,2*m⟩
  have hnot : extra∉ts := by
    intro ht
    have hs := (hselected extra ht).2.2.2
    dsimp [extra,n] at hs
    unfold LowBand HighBand at hs
    omega
  have hextra : TrianglePredicate n L extra := by
    apply wrap_triangle m hm h hh hcap
    simpa only [n,Nat.add_sub_cancel_right] using hcut
  refine ⟨L,hp,hsimple,extra::ts,List.nodup_cons.mpr ⟨hnot,hts⟩,?_,?_⟩
  · intro t ht
    rcases List.mem_cons.mp ht with ht | ht
    · simpa only [ht] using hextra
    · rcases hselected t ht with ⟨h1,h2,h3,hs⟩
      exact selected_preserved n hn h hh hcut t.i t.j t.k h1 h2 h3 hs
  · simpa only [List.length_cons] using Nat.add_le_add_right hcount 1

theorem one_cap_lower_bound (m : ℕ) (hm : 1≤m) :
    LowerBound (2*m+1) (FurediPalasti.lower (2*m+1)+1) :=
  (one_cap_simple_lower_bound m hm).classical

#print axioms wrap_triangle
#print axioms one_cap_simple_lower_bound
end Kobon.FurediPalastiWrap
