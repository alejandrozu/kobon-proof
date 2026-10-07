import Kobon.UpperOpenMathPartialTripleMirror
import Kobon.UpperOpenMathActualMatching
import Kobon.UpperOpenMathCapHeavyTriples

/-!
# A marked triple edge forces a low-resource neighbor

If both rays beside a shared core ray are ordinary and shared at a triple
core, the neighboring triple cannot share either of its two neighboring
ordinary rays. Its outer two sectors are absent; only two shared rays can
remain. Thus its ordinary degree is at most one and its core degree at most
two. The actual specialization derives all matching data from certificates.
-/
namespace Kobon.UpperOpenMathMarkedPoverty
open Cells FanGeometry UpperVertexBudget UpperTriangleIncidence UpperSharedIncidence
  UpperCoreExtraction UpperOpenMathRadialOrder UpperOpenMathActualFans
  UpperOpenMathCapHeavyTriples Finset

theorem finite_shared_subset (T : Finset (ZMod 6))
    (h1 : (1 : ZMod 6)∉T) (h4 : (4 : ZMod 6)∉T) :
    UpperOpenMathPartialTriple.finite_shared T⊆{0,3} := by
  have h : ∀ T : Finset (ZMod 6), (1 : ZMod 6)∉T → (4 : ZMod 6)∉T →
      UpperOpenMathPartialTriple.finite_shared T⊆{0,3} := by decide +kernel
  exact h T h1 h4

theorem finite_extremal_next : ∀ S : Finset (ZMod 6), S.card=3 →
    (∀ z∈S,z+1∉S) → (0 : ZMod 6)∉S → (1 : ZMod 6)∈S := by
  decide +kernel

theorem bounds_of_missing_neighbor_sharing_sum {n : ℕ} {L : ℕ → Line ℝ}
    (g : UpperFan.Sectors n 3 L) (b : ZMod 6) (hcore : b∈g.coreShared)
    (op : OrdinaryAt n L (g.point (b-1)))
    (on : OrdinaryAt n L (g.point (b+1)))
    (np : b-1∉g.ordinaryShared) (nn : b+1∉g.ordinaryShared) :
    g.ordinaryShared.card≤1 ∧ g.ordinaryShared.card+g.coreShared.card≤2 := by
  classical
  let f := UpperOpenMathRotation.Sectors.shift g b
  have h0 : (0 : ZMod 6)∈f.coreShared := by
    apply (UpperOpenMathRotation.Sectors.shift_mem_coreShared g b 0).mpr
    simpa only [add_zero] using hcore
  have h5 : b+(5 : ZMod 6)=b-1 := by
    have he : (5 : ZMod 6)= -1 := by decide
    rw [he]; ring
  have op5 : OrdinaryAt n L (f.point 5) := by
    simpa only [f,UpperOpenMathRotation.Sectors.shift_point,h5] using op
  have on1 : OrdinaryAt n L (f.point 1) := on
  have np5 : (5 : ZMod 6)∉f.ordinaryShared := by
    intro h
    exact np (by simpa only [h5] using
      (UpperOpenMathRotation.Sectors.shift_mem_ordinaryShared g b 5).mp h)
  have nn1 : (1 : ZMod 6)∉f.ordinaryShared := by
    intro h
    exact nn ((UpperOpenMathRotation.Sectors.shift_mem_ordinaryShared g b 1).mp h)
  have hs := (mem_filter.mp (mem_sdiff.mp h0).1)
  have ht0 : (0 : ZMod 6)∈f.triangular := hs.1
  have ht5 : (5 : ZMod 6)∈f.triangular := by
    have he : (0 : ZMod 6)-1=5 := by decide
    simpa only [he] using hs.2
  have ht1 : (1 : ZMod 6)∉f.triangular := by
    intro h
    apply nn1
    rw [f.mem_ordinaryShared]
    exact ⟨h,by simpa using ht0,on1⟩
  have ht4 : (4 : ZMod 6)∉f.triangular := by
    intro h
    apply np5
    rw [f.mem_ordinaryShared]
    exact ⟨ht5,by simpa using h,op5⟩
  have hsub : f.shared⊆{0,3} := finite_shared_subset f.triangular ht1 ht4
  have hosub : f.ordinaryShared⊆{3} := by
    intro z hz
    have hm := hsub (f.ordinaryShared_subset hz)
    simp only [mem_insert,mem_singleton] at hm
    rcases hm with rfl|rfl
    · exact False.elim ((mem_sdiff.mp h0).2 hz)
    · simp
  have ho := card_le_card hosub
  have hsh := card_le_card hsub
  have split := f.shared_card_split
  simp only [card_singleton] at ho
  have pair_card : ({0,3} : Finset (ZMod 6)).card=2 := by decide
  rw [pair_card] at hsh
  have hh : f.ordinaryShared.card≤1 ∧ f.ordinaryShared.card+f.coreShared.card≤2 := by omega
  simpa only [f,UpperOpenMathRotation.Sectors.shift_ordinaryShared_card,
    UpperOpenMathRotation.Sectors.shift_coreShared_card] using hh

theorem marked_neighbor_poverty_sum_card {n r s : ℕ}
    [NeZero (2*r)] [NeZero (2*s)] {L : ℕ → Line ℝ}
    (hr : r=3) (hs : s=3) (hL : NoParallel n L)
    (f : UpperFan.Sectors n r L) (g : UpperFan.Sectors n s L)
    (a : ZMod (2*r)) (b : ZMod (2*s))
    (fprev : a-1∈f.ordinaryShared) (fnext : a+1∈f.ordinaryShared)
    (gcore : b∈g.coreShared)
    (centerg : g.center=f.point a) (pointg : g.point b=f.center)
    (rightg : g.point (b-1)=f.point (a+1))
    (leftg : g.point (b+1)=f.point (a-1))
    (positive : ∀ z, 0<areaDet f.center (f.point z) (f.point (z+1))) :
    g.ordinaryShared.card≤1 ∧ g.ordinaryShared.card+g.coreShared.card≤2 := by
  have op : OrdinaryAt n L (g.point (b-1)) := by
    rw [rightg]
    exact ((f.mem_ordinaryShared (a+1)).mp fnext).2.2
  have on : OrdinaryAt n L (g.point (b+1)) := by
    rw [leftg]
    exact ((f.mem_ordinaryShared (a-1)).mp fprev).2.2
  have np : b-1∉g.ordinaryShared := by
    intro h
    exact UpperOpenMathPartialTriple.incompatible_partial_triple_fans_card hr hs hL
      f g a b fprev h centerg pointg rightg leftg positive
  have nn : b+1∉g.ordinaryShared := by
    intro h
    exact UpperOpenMathPartialTripleMirror.incompatible_following_partial_triple_fans_card hr hs hL
      f g a b fnext h centerg pointg rightg leftg positive
  subst s
  exact bounds_of_missing_neighbor_sharing_sum g b gcore op on np nn

theorem ordinary_neighbors_of_two_one_card {n r : ℕ} [NeZero (2*r)]
    {L : ℕ → Line ℝ} (hr : r=3) (f : UpperFan.Sectors n r L)
    (hord : f.ordinaryShared.card=2) (hcore : f.coreShared.card=1)
    (a : ZMod (2*r)) (ha : a∈f.coreShared) :
    a-1∈f.ordinaryShared ∧ a+1∈f.ordinaryShared := by
  subst r
  let g := UpperOpenMathRotation.Sectors.shift f a
  have hgo : g.ordinaryShared.card=2 := by
    rw [UpperOpenMathRotation.Sectors.shift_ordinaryShared_card]
    exact hord
  have hgc : g.coreShared.card=1 := by
    rw [UpperOpenMathRotation.Sectors.shift_coreShared_card]
    exact hcore
  have hzero : (0 : ZMod 6)∈g.coreShared := by
    apply (UpperOpenMathRotation.Sectors.shift_mem_coreShared f a 0).mpr
    simpa only [add_zero] using ha
  have hf := (UpperOpenMathPartialTriple.ordinary_neighbors_of_two_one g hgo hgc hzero).1
  exact ⟨UpperOpenMathPartialTriple.ordinary_previous_of_two_one_card rfl f hord hcore a ha,
    (UpperOpenMathRotation.Sectors.shift_mem_ordinaryShared f a 1).mp hf⟩

theorem ordinary_neighbors_of_extremal_card {n r : ℕ} [NeZero (2*r)]
    {L : ℕ → Line ℝ} (hr : r=3) (f : UpperFan.Sectors n r L)
    (hcard : 3≤f.ordinaryShared.card) (a : ZMod (2*r)) (ha : a∈f.coreShared) :
    a-1∈f.ordinaryShared ∧ a+1∈f.ordinaryShared := by
  subst r
  let g := UpperOpenMathRotation.Sectors.shift f a
  have hgc : g.ordinaryShared.card=3 := by
    have hl := g.ordinary_shared_card_le (by decide)
    have hg : 3≤g.ordinaryShared.card := by
      rw [UpperOpenMathRotation.Sectors.shift_ordinaryShared_card]
      exact hcard
    omega
  have hsep (z : ZMod 6) (hz : z∈g.ordinaryShared) : z+1∉g.ordinaryShared := by
    intro hn
    obtain ⟨j,hj⟩ := g.no_run (by decide) z
    have hjv : j.val=0 ∨ j.val=1 := by have := j.isLt; omega
    rcases hjv with hjv|hjv
    · simp only [hjv,Nat.cast_zero,add_zero] at hj
      exact hj hz
    · simp only [hjv,Nat.cast_one] at hj
      exact hj hn
  have hzero : (0 : ZMod 6)∉g.ordinaryShared := by
    intro h
    exact (mem_sdiff.mp ha).2 (by simpa only [add_zero] using
      (UpperOpenMathRotation.Sectors.shift_mem_ordinaryShared f a 0).mp h)
  have h1 := finite_extremal_next g.ordinaryShared hgc hsep hzero
  exact ⟨UpperOpenMathPartialTriple.ordinary_previous_of_extremal_card rfl f hcard a ha,
    (UpperOpenMathRotation.Sectors.shift_mem_ordinaryShared f a 1).mp h1⟩

/-- Every actual shared-core neighbor of an extremal triple has ordinary
sharing degree at most one and total sharing degree at most two. -/
theorem certificate_extremal_neighbor_sum {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (c d : Point) (hc : c∈core n L) (hd : d∈core n L)
    (rc : (supports n L c).card=3) (rd : (supports n L d).card=3)
    (extremal : ordinaryDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) c=3)
    (edge : {c,d}∈twoCoreEdges n L (fun a => ofPredicate n L (tri a) hL (ht a))) :
    ordinaryDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) d≤1 ∧
      ordinaryDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) d+
        coreDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) d≤2 := by
  classical
  let G := fun a => ofPredicate n L (tri a) hL (ht a)
  letI : NeZero (2*(supports n L c).card) := ⟨by omega⟩
  letI : NeZero (2*(supports n L d).card) := ⟨by omega⟩
  let D := atPoint n L hL hn c
  let E := atPoint n L hL hn d
  let f := fan n L hL hn tri ht c (mem_filter.mp hc).1 D (by omega)
  let g := fan n L hL hn tri ht d (mem_filter.mp hd).1 E (by omega)
  have used := (mem_filter.mp (mem_sdiff.mp edge).1).1
  have neq : d≠c := by
    intro he
    have hcard := used_edge_card G used
    simp only [he,insert_eq_of_mem (mem_singleton_self c),card_singleton] at hcard
    omega
  obtain ⟨z,hz⟩ := UpperOpenMathSectorRecords.used_edge_has_ray n L hL hn tri ht c
    (mem_filter.mp hc).1 D d neq used
  change f.point z=d at hz
  have fcore : z∈f.coreShared :=
    (fan_core_iff n L hL hn tri ht c (mem_filter.mp hc).1 D (by omega) hi hc z).mpr
      (by rw [hz]; exact edge)
  obtain ⟨w,gcore,gw,right,left⟩ := UpperOpenMathActualMatching.certificate_neighbor_matching
    n L hL hn tri hi ht c d hc hd D E (by omega) (by omega) z fcore hz.symm
  have hfo : 3≤f.ordinaryShared.card := by
    rw [fan_ordinary_card n L hL hn tri ht c (mem_filter.mp hc).1 D (by omega) hi hc]
    exact Nat.le_of_eq extremal.symm
  obtain ⟨prev,next⟩ := ordinary_neighbors_of_extremal_card rc f hfo z fcore
  have poor := marked_neighbor_poverty_sum_card rc rd hL f g z w prev next gcore hz.symm gw right left
    (fan_positive n L hL hn tri ht c (mem_filter.mp hc).1 D (by omega))
  rw [fan_ordinary_card n L hL hn tri ht d (mem_filter.mp hd).1 E (by omega) hi hd,
    fan_core_card n L hL hn tri ht d (mem_filter.mp hd).1 E (by omega) hi hd] at poor
  exact poor

/-- Separate degree bounds retained as a convenience consequence. -/
theorem certificate_extremal_neighbor_low {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (c d : Point) (hc : c∈core n L) (hd : d∈core n L)
    (rc : (supports n L c).card=3) (rd : (supports n L d).card=3)
    (extremal : ordinaryDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) c=3)
    (edge : {c,d}∈twoCoreEdges n L (fun a => ofPredicate n L (tri a) hL (ht a))) :
    ordinaryDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) d≤1 ∧
      coreDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) d≤2 := by
  have h := certificate_extremal_neighbor_sum n L hL hn tri hi ht c d hc hd rc rd extremal edge
  exact ⟨h.1,by omega⟩

/-- The same low-resource target is forced by the partial four-run source,
in addition to the full ordinary-degree-three source. -/
theorem certificate_cap_heavy_neighbor_sum {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (c d : Point) (hc : c∈core n L) (hd : d∈core n L)
    (rc : (supports n L c).card=3) (rd : (supports n L d).card=3)
    (capheavy : ordinaryDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) c=3 ∨
      (ordinaryDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) c=2 ∧
      coreDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) c=1))
    (edge : {c,d}∈twoCoreEdges n L (fun a => ofPredicate n L (tri a) hL (ht a))) :
    ordinaryDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) d≤1 ∧
      ordinaryDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) d+
        coreDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) d≤2 := by
  classical
  rcases capheavy with ext|⟨hord,hcore⟩
  · exact certificate_extremal_neighbor_sum n L hL hn tri hi ht c d hc hd rc rd ext edge
  let G := fun a => ofPredicate n L (tri a) hL (ht a)
  letI : NeZero (2*(supports n L c).card) := ⟨by omega⟩
  letI : NeZero (2*(supports n L d).card) := ⟨by omega⟩
  let D := atPoint n L hL hn c
  let E := atPoint n L hL hn d
  let f := fan n L hL hn tri ht c (mem_filter.mp hc).1 D (by omega)
  let g := fan n L hL hn tri ht d (mem_filter.mp hd).1 E (by omega)
  have used := (mem_filter.mp (mem_sdiff.mp edge).1).1
  have neq : d≠c := by
    intro he
    have hcard := used_edge_card G used
    simp only [he,insert_eq_of_mem (mem_singleton_self c),card_singleton] at hcard
    omega
  obtain ⟨z,hz⟩ := UpperOpenMathSectorRecords.used_edge_has_ray n L hL hn tri ht c
    (mem_filter.mp hc).1 D d neq used
  change f.point z=d at hz
  have fcore : z∈f.coreShared :=
    (fan_core_iff n L hL hn tri ht c (mem_filter.mp hc).1 D (by omega) hi hc z).mpr
      (by rw [hz]; exact edge)
  obtain ⟨w,gcore,gw,right,left⟩ := UpperOpenMathActualMatching.certificate_neighbor_matching
    n L hL hn tri hi ht c d hc hd D E (by omega) (by omega) z fcore hz.symm
  have hfo : f.ordinaryShared.card=2 := by
    rw [fan_ordinary_card n L hL hn tri ht c (mem_filter.mp hc).1 D (by omega) hi hc]
    exact hord
  have hfc : f.coreShared.card=1 := by
    rw [fan_core_card n L hL hn tri ht c (mem_filter.mp hc).1 D (by omega) hi hc]
    exact hcore
  obtain ⟨prev,next⟩ := ordinary_neighbors_of_two_one_card rc f hfo hfc z fcore
  have poor := marked_neighbor_poverty_sum_card rc rd hL f g z w prev next gcore hz.symm gw right left
    (fan_positive n L hL hn tri ht c (mem_filter.mp hc).1 D (by omega))
  rw [fan_ordinary_card n L hL hn tri ht d (mem_filter.mp hd).1 E (by omega) hi hd,
    fan_core_card n L hL hn tri ht d (mem_filter.mp hd).1 E (by omega) hi hd] at poor
  exact poor

#print axioms marked_neighbor_poverty_sum_card
#print axioms certificate_extremal_neighbor_sum
#print axioms certificate_extremal_neighbor_low
#print axioms certificate_cap_heavy_neighbor_sum
end Kobon.UpperOpenMathMarkedPoverty
