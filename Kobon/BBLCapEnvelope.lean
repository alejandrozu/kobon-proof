import Kobon.BBLCapSigns

/-! Cap-envelope signs from the realized crossing order.
Only auxiliary graph equations, ordered intercepts, and slope signs are
used here. The analytic construction of the crossing order is separate.
-/
namespace Kobon.BBLCapEnvelope
open Exterior HybridBoundary BBLExtrema BBLTriangles BBLRowOrder BBLCount BBLRowGeometry
  BBLCaps BBLCapSigns
set_option maxHeartbeats 10000000

theorem between_product (p a b : ℝ)
    (h : (a≤p ∧ p≤b) ∨ (b≤p ∧ p≤a)) : (a-p)*(b-p)≤0 := by
  rcases h with ⟨h1,h2⟩ | ⟨h1,h2⟩
  · exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
  · exact mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)

theorem between_evaluation_product (r l m s w : Line ℝ)
    (hlm : det l m ≠ 0) (hls : det l s ≠ 0) (hlr : det l r ≠ 0)
    (hwl : det w l ≠ 0)
    (hin : (projection w (intersection l m)≤projection w (intersection l r) ∧
       projection w (intersection l r)≤projection w (intersection l s)) ∨
      (projection w (intersection l s)≤projection w (intersection l r) ∧
       projection w (intersection l r)≤projection w (intersection l m))) :
    affineEval r (intersection l m)*affineEval r (intersection l s)≤0 := by
  rw [evaluation_from_intersection r l m w hlm hlr hwl,
    evaluation_from_intersection r l s w hls hlr hwl]
  have hh := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg (derivative r l w))
    (between_product _ _ _ hin)
  nlinarith only [hh]

theorem key_evaluation_product (r : Nat) (L : Nat → Line ℝ) (w : Line ℝ)
    (hp : NoParallel (8*r+1) L) (hw : Admissible (8*r+1) L w)
    (horder : CrossingOrder r L w) (i : Nat) (hi : i≤4*r)
    (a b c : Fin (8*r+1))
    (ha : a.val≠4*r+i) (hb : b.val≠4*r+i) (hc : c.val≠4*r+i) :
    (keyOutside (crossKey r i c) (crossKey r i a) (crossKey r i b) →
      0≤affineEval (L c) (intersection (L (4*r+i)) (L a))*
        affineEval (L c) (intersection (L (4*r+i)) (L b))) ∧
    (¬keyOutside (crossKey r i c) (crossKey r i a) (crossKey r i b) →
      affineEval (L c) (intersection (L (4*r+i)) (L a))*
        affineEval (L c) (intersection (L (4*r+i)) (L b))≤0) := by
  let u : Fin (8*r+1) := ⟨4*r+i,by omega⟩
  have hua : u≠a := by intro h; have := congrArg Fin.val h; dsimp [u] at this; omega
  have hub : u≠b := by intro h; have := congrArg Fin.val h; dsimp [u] at this; omega
  have huc : u≠c := by intro h; have := congrArg Fin.val h; dsimp [u] at this; omega
  have hda := det_ne_of_ne _ L hp u a hua
  have hdb := det_ne_of_ne _ L hp u b hub
  have hdc := det_ne_of_ne _ L hp u c huc
  have hdw : det w (L u)≠0 := by rw [det_skew]; exact neg_ne_zero.mpr (hw u)
  constructor
  · rintro (⟨h1,h2⟩ | ⟨h1,h2⟩)
    · apply outside_evaluation_product _ _ _ _ _ hda hdb hdc hdw
      exact Or.inl ⟨horder i hi c a hc ha h1,horder i hi c b hc hb h2⟩
    · apply outside_evaluation_product _ _ _ _ _ hda hdb hdc hdw
      exact Or.inr ⟨horder i hi a c ha hc h1,horder i hi b c hb hc h2⟩
  · intro hn
    have hbetween :
        (crossKey r i a≤crossKey r i c ∧ crossKey r i c≤crossKey r i b) ∨
        (crossKey r i b≤crossKey r i c ∧ crossKey r i c≤crossKey r i a) := by
      unfold keyOutside at hn
      omega
    apply between_evaluation_product _ _ _ _ _ hda hdb hdc hdw
    rcases hbetween with ⟨h1,h2⟩ | ⟨h1,h2⟩
    · exact Or.inl ⟨horder i hi a c ha hc h1,horder i hi c b hc hb h2⟩
    · exact Or.inr ⟨horder i hi b c hb hc h1,horder i hi c a hc ha h2⟩

theorem graph_horizontal_intersection (m a : ℝ) (hm : m≠0) :
    intersection (graphLine m a) (graphLine 0 0)=(a,0) := by
  apply Prod.ext
  · dsimp [intersection,vertex,det,graphLine]
    field_simp [hm]
    <;> ring
  · simp [intersection,vertex,det,graphLine]

theorem graph_reference_sign (r i k : Nat) (hi : i<4*r) (hk : k<4*r) (hik : i≠k)
    (m a : Nat → ℝ)
    (hmneg : ∀ t<2*r, m t<0) (hmpos : ∀ t, 2*r≤t → t<4*r → 0<m t)
    (ha : ∀ s t, s<t → t<4*r → a s<a t) :
    (0<m k*(a i-a k) ↔ positiveAtHorizontal r i k) ∧ m k*(a i-a k)≠0 := by
  by_cases hkn : k<2*r
  · have hm := hmneg k hkn
    by_cases hik' : i<k
    · have haa := ha i k hik' hk
      have hv : 0<m k*(a i-a k) := mul_pos_of_neg_of_neg hm (by linarith)
      exact ⟨by simp [positiveAtHorizontal,hkn,hik',hv],ne_of_gt hv⟩
    · have hki : k < i := by omega
      have haa := ha k i hki hi
      have hv : m k*(a i-a k)<0 := mul_neg_of_neg_of_pos hm (by linarith)
      have hkn' : ¬2*r≤k := by omega
      exact ⟨by simp [positiveAtHorizontal,hkn,hik',hkn',not_lt_of_ge (le_of_lt hv)],ne_of_lt hv⟩
  · have hkn' : 2*r≤k := by omega
    have hm := hmpos k hkn' hk
    by_cases hki : k < i
    · have haa := ha k i hki hi
      have hv : 0<m k*(a i-a k) := mul_pos hm (by linarith)
      exact ⟨by simp [positiveAtHorizontal,hkn,hkn',hki,hv],ne_of_gt hv⟩
    · have hik' : i<k := by omega
      have haa := ha i k hik' hk
      have hv : m k*(a i-a k)<0 := mul_neg_of_pos_of_neg hm (by linarith)
      exact ⟨by simp [positiveAtHorizontal,hkn,hki,not_lt_of_ge (le_of_lt hv)],ne_of_lt hv⟩

theorem sign_transfer (x y : ℝ) (P Q S : Prop) (hy : y≠0)
    (hp : 0<y ↔ P) (hs : S ↔ (Q ↔ P))
    (hout : S → 0≤x*y) (hin : ¬S → x*y≤0) :
    (Q → 0≤x) ∧ (¬Q → x≤0) := by
  constructor
  · intro hq
    by_cases hP : P
    · have hS : S := hs.mpr (by simp [hq,hP])
      have hyp := hp.mpr hP
      rcases mul_nonneg_iff.mp (hout hS) with ⟨h1,h2⟩ | ⟨h1,h2⟩ <;> linarith
    · have hS : ¬S := by rw [hs]; simp [hq,hP]
      have hyn : y<0 := by
        rcases lt_or_gt_of_ne hy with h | h
        · exact h
        · exact False.elim (hP (hp.mp h))
      rcases mul_nonpos_iff.mp (hin hS) with ⟨h1,h2⟩ | ⟨h1,h2⟩ <;> linarith
  · intro hq
    by_cases hP : P
    · have hS : ¬S := by rw [hs]; simp [hq,hP]
      have hyp := hp.mpr hP
      rcases mul_nonpos_iff.mp (hin hS) with ⟨h1,h2⟩ | ⟨h1,h2⟩ <;> linarith
    · have hS : S := hs.mpr (by simp [hq,hP])
      have hyn : y<0 := by
        rcases lt_or_gt_of_ne hy with h | h
        · exact h
        · exact False.elim (hP (hp.mp h))
      rcases mul_nonneg_iff.mp (hout hS) with ⟨h1,h2⟩ | ⟨h1,h2⟩ <;> linarith

theorem cap_left_endpoint (r j k : Nat) (hr : 1≤r) (hj : j<4*r-1)
    (hcentral : j≠2*r-1) (hk : k<4*r) (hki : k≠capRow r j)
    (L : Nat → Line ℝ) (w : Line ℝ) (m a : Nat → ℝ)
    (hp : NoParallel (8*r+1) L) (hw : Admissible (8*r+1) L w)
    (horder : CrossingOrder r L w)
    (hgraph : ∀ t<4*r, L (4*r+t)=graphLine (m t) (a t))
    (hzero : L (8*r)=graphLine 0 0)
    (hmneg : ∀ t<2*r, m t<0) (hmpos : ∀ t, 2*r≤t → t<4*r → 0<m t)
    (ha : ∀ s t, s<t → t<4*r → a s<a t) :
    (j%2=0 → 0≤affineEval (L (4*r+k))
      (intersection (L (4*r+capRow r j)) (L j))) ∧
    (j%2≠0 → affineEval (L (4*r+k))
      (intersection (L (4*r+capRow r j)) (L j))≤0) := by
  let i := capRow r j
  have hi : i<4*r := capRow_ne_horizontal r j hr hj hcentral
  have him : m i≠0 := by
    by_cases hin : i<2*r
    · exact ne_of_lt (hmneg i hin)
    · exact ne_of_gt (hmpos i (by omega) hi)
  have href : affineEval (L (4*r+k))
      (intersection (L (4*r+i)) (L (8*r)))=m k*(a i-a k) := by
    rw [hgraph k hk,hgraph i hi,hzero,graph_horizontal_intersection _ _ him]
    dsimp [affineEval,graphLine]
    ring
  obtain ⟨hypos,hyne⟩ := graph_reference_sign r i k hi hk (Ne.symm hki) m a hmneg hmpos ha
  let aa : Fin (8*r+1) := ⟨j,by omega⟩
  let bb : Fin (8*r+1) := ⟨8*r,by omega⟩
  let cc : Fin (8*r+1) := ⟨4*r+k,by omega⟩
  have haa : aa.val≠4*r+i := by dsimp [aa]; omega
  have hbb : bb.val≠4*r+i := by dsimp [bb]; omega
  have hcc : cc.val≠4*r+i := by dsimp [cc]; omega
  have hA : crossKey r i aa=oldKey j := by simp [crossKey,aa,show j<4*r by omega]
  have hB : crossKey r i bb=horizontalKey r i := by
    have hh : crossKey r i bb=newKey (2*r) i (4*r) := by
      dsimp [crossKey,bb]
      rw [if_neg (by omega)]
      congr 1 <;> push_cast <;> ring
    rw [hh,horizontalKey_eq r i hi]
  have hC : crossKey r i cc=newKey (2*r) i k := by
    dsimp [crossKey,cc]
    rw [if_neg (by omega)]
    congr 1 <;> push_cast <;> ring
  have hsign : keyOutside (crossKey r i cc) (crossKey r i aa) (crossKey r i bb) ↔
      (j%2=0 ↔ positiveAtHorizontal r i k) := by
    rw [hA,hB,hC]
    exact cap_key_signs r j k hr hj hcentral hk hki
  have hproducts := key_evaluation_product r L w hp hw horder i (le_of_lt hi)
    aa bb cc haa hbb hcc
  apply sign_transfer _ (affineEval (L (4*r+k)) (intersection (L (4*r+i)) (L (8*r))))
    (positiveAtHorizontal r i k) (j%2=0)
    (keyOutside (crossKey r i cc) (crossKey r i aa) (crossKey r i bb))
    (by simpa only [href] using hyne) (by simpa only [href] using hypos) hsign
  · exact hproducts.1
  · exact hproducts.2

#print axioms cap_left_endpoint

theorem cap_right_endpoint (r j k : Nat) (hr : 1≤r) (hj : j<4*r-1)
    (hcentral : j≠2*r-1) (hk : k<4*r) (hki : k≠capRow r j)
    (L : Nat → Line ℝ) (w : Line ℝ) (m a : Nat → ℝ)
    (hp : NoParallel (8*r+1) L) (hs : NoConcurrent (8*r+1) L)
    (hw : Admissible (8*r+1) L w) (horder : CrossingOrder r L w)
    (hgraph : ∀ t<4*r, L (4*r+t)=graphLine (m t) (a t))
    (hzero : L (8*r)=graphLine 0 0)
    (hmneg : ∀ t<2*r, m t<0) (hmpos : ∀ t, 2*r≤t → t<4*r → 0<m t)
    (ha : ∀ s t, s<t → t<4*r → a s<a t) :
    (j%2=0 → 0≤affineEval (L (4*r+k))
      (intersection (L (4*r+capRow r j)) (L (j+1)))) ∧
    (j%2≠0 → affineEval (L (4*r+k))
      (intersection (L (4*r+capRow r j)) (L (j+1)))≤0) := by
  let i := capRow r j
  have hi : i≤4*r := capRow_le r j hr hj
  let u : Fin (8*r+1) := ⟨4*r+i,by omega⟩
  let v : Fin (8*r+1) := ⟨4*r+k,by omega⟩
  let a0 : Fin (8*r+1) := ⟨j,by omega⟩
  let b0 : Fin (8*r+1) := ⟨j+1,by omega⟩
  have hua : u≠a0 := by intro h; have := congrArg Fin.val h; dsimp [u,a0] at this; omega
  have hub : u≠b0 := by intro h; have := congrArg Fin.val h; dsimp [u,b0] at this; omega
  have huv : u≠v := by intro h; have := congrArg Fin.val h; dsimp [u,v] at this; omega
  have hva : v≠a0 := by intro h; have := congrArg Fin.val h; dsimp [v,a0] at this; omega
  have hau : a0<u := by change j < 4*r+i; omega
  have hda := det_ne_of_ne _ L hp u a0 hua
  have hdb := det_ne_of_ne _ L hp u b0 hub
  have hdv := det_ne_of_ne _ L hp u v huv
  have hdw : det w (L u)≠0 := by rw [det_skew]; exact neg_ne_zero.mpr (hw u)
  have hside := cap_side r j hr hj L w horder v (by dsimp [v]; omega)
  have hprod := outside_evaluation_product (L v) (L u) (L a0) (L b0) w hda hdb hdv hdw hside
  have hnd := no_concurrent_at_pair _ L hs a0 u v hau hva (Ne.symm huv)
  have hnd' : affineEval (L v) (intersection (L u) (L a0))≠0 := by
    rw [intersection_swap,eval_intersection _ _ _ (hp a0 u hau)]
    exact div_ne_zero hnd (hp a0 u hau)
  have hleft := cap_left_endpoint r j k hr hj hcentral hk hki L w m a hp hw horder
    hgraph hzero hmneg hmpos ha
  change (j%2=0 → 0≤affineEval (L v) (intersection (L u) (L a0))) ∧
    (j%2≠0 → affineEval (L v) (intersection (L u) (L a0))≤0) at hleft
  change (j%2=0 → 0≤affineEval (L v) (intersection (L u) (L b0))) ∧
    (j%2≠0 → affineEval (L v) (intersection (L u) (L b0))≤0)
  constructor
  · intro he
    have hl := hleft.1 he
    rcases mul_nonneg_iff.mp hprod with ⟨h1,h2⟩ | ⟨h1,h2⟩
    · exact h2
    · exfalso; apply hnd'; linarith
  · intro ho
    have hl := hleft.2 ho
    rcases mul_nonneg_iff.mp hprod with ⟨h1,h2⟩ | ⟨h1,h2⟩
    · exfalso; apply hnd'; linarith
    · exact h2

#print axioms cap_right_endpoint

end Kobon.BBLCapEnvelope
