import Kobon.BBLPersistence
import Mathlib.Data.Finset.Card

/-! At most one visible pair can use the distinguished line. Consequently
the strict-continuity preservation theorem loses at most one old pair. -/
namespace Kobon.BBLVisibleRetention
open Exterior HybridBoundary BBLExtrema BBLTriangles BBLPersistence

theorem zero_visible_j_unique (n i j : Nat) (L : Nat → Line ℝ) (w : Line ℝ)
    (hp : NoParallel n L) (hs : NoConcurrent n L) (hw : Admissible n L w)
    (hi : VisiblePair n L w ⟨0,i,n⟩) (hj : VisiblePair n L w ⟨0,j,n⟩) : i=j := by
  have hip : 0 < i := hi.1
  have hjp : 0 < j := hj.1
  have hin : i<n := hi.2.1
  have hjn : j<n := hj.2.1
  have hzn : 0<n := by omega
  have hm1 := visible_extremal n L w hp hw ⟨0,i,n⟩ hi ⟨j,hjn⟩ (by simpa using ne_of_gt hjp)
  have hm2 := visible_extremal n L w hp hw ⟨0,j,n⟩ hj ⟨i,hin⟩ (by simpa using ne_of_gt hip)
  have heq : projection w (intersection (L 0) (L i))=
      projection w (intersection (L 0) (L j)) := le_antisymm hm2 hm1
  by_contra hij
  have hd0i := hp ⟨0,hzn⟩ ⟨i,hin⟩ hip
  have hd0j := hp ⟨0,hzn⟩ ⟨j,hjn⟩ hjp
  have hdw : det w (L 0)≠0 := by
    rw [det_skew]
    exact neg_ne_zero.mpr (hw ⟨0,hzn⟩)
  have hev := evaluation_from_intersection (L j) (L 0) (L i) w hd0i hd0j hdw
  rw [heq,sub_self,mul_zero] at hev
  have hne := no_concurrent_at_pair n L hs ⟨0,hzn⟩ ⟨i,hin⟩ ⟨j,hjn⟩ hip
    (by intro h; have hh := congrArg Fin.val h; dsimp at hh; omega)
    (by intro h; exact hij (congrArg Fin.val h).symm)
  rw [eval_intersection _ _ _ hd0i] at hev
  exact (div_ne_zero hne hd0i) hev

theorem zero_visible_unique (n : Nat) (L : Nat → Line ℝ) (w : Line ℝ)
    (hp : NoParallel n L) (hs : NoConcurrent n L) (hw : Admissible n L w)
    (s t : Triple) (hsvis : VisiblePair n L w s) (htvis : VisiblePair n L w t)
    (hs0 : s.i=0) (ht0 : t.i=0) : s=t := by
  have hsk : s.k=n := hsvis.2.2.1
  have htk : t.k=n := htvis.2.2.1
  cases s with
  | mk si sj sk =>
    cases t with
    | mk ti tj tk =>
      change si=0 at hs0
      change ti=0 at ht0
      change sk=n at hsk
      change tk=n at htk
      subst si; subst ti; subst sk; subst tk
      have hj := zero_visible_j_unique n sj tj L w hp hs hw hsvis htvis
      cases hj
      rfl

theorem retain_all_but_one (n : Nat) (L : Nat → Line ℝ) (w : Line ℝ)
    (hp : NoParallel n L) (hs : NoConcurrent n L) (hw : Admissible n L w)
    (ts : List Triple) (hnd : ts.Nodup) (hv : ∀ t∈ts, VisiblePair n L w t) :
    ts.length≤(ts.filter (fun t => decide (t.i≠0))).length+1 := by
  let zeros := ts.filter (fun t => decide (t.i=0))
  have hzn : zeros.Nodup := hnd.filter _
  have hzcard : zeros.toFinset.card≤1 := by
    apply Finset.card_le_one.mpr
    intro s hs' t ht'
    have hsm : s∈zeros := List.mem_toFinset.mp hs'
    have htm : t∈zeros := List.mem_toFinset.mp ht'
    simp only [zeros,List.mem_filter,decide_eq_true_eq] at hsm htm
    exact zero_visible_unique n L w hp hs hw s t (hv s hsm.1) (hv t htm.1) hsm.2 htm.2
  have hzlen : zeros.length≤1 := by
    rwa [List.toFinset_card_of_nodup hzn] at hzcard
  have hsplit := List.length_eq_length_filter_add (l:=ts) (fun t => decide (t.i=0))
  have hneg : (fun t : Triple => !decide (t.i=0))=(fun t => decide (t.i≠0)) := by
    funext t
    simp
  rw [hneg] at hsplit
  dsimp [zeros] at hzlen
  omega

#print axioms zero_visible_unique
#print axioms retain_all_but_one
end Kobon.BBLVisibleRetention
