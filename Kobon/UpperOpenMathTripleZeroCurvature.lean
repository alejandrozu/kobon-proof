import Kobon.UpperOpenMathHighNeighborCharts

/-! Zero-curvature triple cores cannot close. The two possible local types
are (ordinary,core) degrees (2,2) and (0,6). Their actual shared-side matching
prevents the types from touching, and each closed pure type is impossible. -/
namespace Kobon.UpperOpenMathTripleZeroCurvature
open Cells FanGeometry UpperFan UpperVertexBudget UpperTriangleIncidence
  UpperSharedIncidence UpperCoreExtraction UpperOpenMathRadialOrder
  UpperOpenMathActualFans UpperOpenMathCapHeavyTriples UpperOpenMathCoreComponents
  UpperOpenMathTripleCharts Finset
set_option maxHeartbeats 1000000

theorem normalized_full_incompatible {α : Type*} [Fintype α]
    (G : α → TriangleGeometry)
    (disjoint : Pairwise (fun a b => Disjoint (G a).interior (G b).interior))
    {n r : ℕ} [NeZero (2*r)] {L : ℕ → Line ℝ} (hr : 2≤r)
    (f : UpperFan.Sectors n 3 L) (g : UpperFan.Sectors n r L)
    (df : NormalizedData G f)
    (ginj : Function.Injective g.point) (gnc : ∀ z, g.point z≠g.center)
    (gpos : ∀ z, 0<areaDet g.center (g.point z) (g.point (z+1)))
    (gactual : ∀ z∈g.triangular, Nonempty
      (UpperOpenMathSectorRecords.Occurrence G g.center g.point z))
    (gno : ∀ z, ¬OrdinaryAt n L (g.point z))
    (z : ZMod (2*3)) (w : ZMod (2*r))
    (fz : z∈f.coreShared) (gw : w∈g.coreShared)
    (gc : g.center=f.point z) (gp : g.point w=f.center) : False := by
  have fs := (mem_sdiff.mp fz).1
  have gs := (mem_sdiff.mp gw).1
  obtain ⟨fo⟩ := df.occurrences (z-1) (mem_filter.mp fs).2
  obtain ⟨fp⟩ := df.occurrences z (mem_filter.mp fs).1
  obtain ⟨go⟩ := gactual (w-1) (mem_filter.mp gs).2
  obtain ⟨gq⟩ := gactual w (mem_filter.mp gs).1
  have matching := UpperOpenMathFiberMatching.neighboring_points_match G disjoint
    (by decide : 2≤3) hr f.center g.center f.point g.point
    df.injective ginj df.noncentral gnc df.positive gpos z w gc gp fo fp go gq
  have cases : z=1 ∨ z=2 := by simpa only [df.core_eq,mem_insert,mem_singleton] using fz
  rcases cases with rfl|rfl
  · have ho : OrdinaryAt n L (f.point 0) :=
      ((f.mem_ordinaryShared 0).mp (by rw [df.ordinary_eq]; simp)).2.2
    have he : g.point (w+1)=f.point 0 := by simpa using matching.2
    exact gno (w+1) (he.symm ▸ ho)
  · have ho : OrdinaryAt n L (f.point 3) :=
      ((f.mem_ordinaryShared 3).mp (by rw [df.ordinary_eq]; simp)).2.2
    have he : g.point (w-1)=f.point 3 := by
      have hx : (2 : ZMod (2*3))+1=3 := by decide
      simpa only [hx] using matching.1
    exact gno (w-1) (he.symm ▸ ho)

theorem certificate_normalized_full_not_adjacent {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (f : UpperFan.Sectors n 3 L)
    (df : NormalizedData (fun a => ofPredicate n L (tri a) hL (ht a)) f)
    (d : Point) (hd : d∈core n L)
    (full : coreDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) d=
      2*(supports n L d).card)
    (edge : {f.center,d}∈twoCoreEdges n L (fun a => ofPredicate n L (tri a) hL (ht a))) : False := by
  classical
  let G := fun a => ofPredicate n L (tri a) hL (ht a)
  have used := (mem_filter.mp (mem_sdiff.mp edge).1).1
  have hne : d≠f.center := by
    intro he
    have hh := used_edge_card G used
    simp only [he,insert_eq_of_mem (mem_singleton_self f.center),card_singleton] at hh
    omega
  obtain ⟨z,fz,fp⟩ := UpperOpenMathTwoTwoCore.reverse_core_label G f df.toChartData d hne edge
  have rd := core_multiplicity n L hL hd
  letI : NeZero (2*(supports n L d).card) := ⟨by omega⟩
  let D := atPoint n L hL hn d
  let g := fan n L hL hn tri ht d (mem_filter.mp hd).1 D (by omega)
  have hf : g.coreShared.card=2*(supports n L d).card := by
    rw [fan_core_card n L hL hn tri ht d (mem_filter.mp hd).1 D (by omega) hi hd]
    exact full
  have all := (UpperOpenMathFullCoreFans.core_full g hf).1
  have gno (w : ZMod (2*(supports n L d).card)) : ¬OrdinaryAt n L (g.point w) := by
    have hw : w∈g.coreShared := by rw [all]; exact mem_univ w
    exact (mem_filter.mp (fan_core_endpoint n L hL hn tri ht d (mem_filter.mp hd).1 D (by omega) hi hd w hw)).2
  have rev : {d,f.center}∈usedEdges G := by simpa only [pair_comm] using used
  obtain ⟨w,wp⟩ := UpperOpenMathSectorRecords.used_edge_has_ray n L hL hn tri ht d
    (mem_filter.mp hd).1 D f.center hne.symm rev
  change g.point w=f.center at wp
  have gw : w∈g.coreShared := by rw [all]; exact mem_univ w
  have disjoint : Pairwise (fun a b => Disjoint (G a).interior (G b).interior) := by
    intro a b hab
    exact distinct_interiors_disjoint n L _ _ hL (ht a) (ht b) (fun he => hab (hi he))
  have actual : ∀ w∈g.triangular, Nonempty
      (UpperOpenMathSectorRecords.Occurrence G g.center g.point w) := by
    intro w hw
    exact (UpperOpenMathSectorRecords.mem_triangular G d g.point w).mp hw
  exact normalized_full_incompatible G disjoint (by omega) f g df
    (fan_point_injective n L hL hn tri ht d (mem_filter.mp hd).1 D (by omega))
    (fan_point_ne_center n L hL hn tri ht d (mem_filter.mp hd).1 D (by omega))
    (fan_positive n L hL hn tri ht d (mem_filter.mp hd).1 D (by omega)) actual gno
    z w fz gw fp.symm wp

theorem certificate_closed_zero_types_impossible {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (P : Finset Point) (sub : P⊆core n L) (nonempty : P.Nonempty)
    (closed : SharedCoreClosed n L (fun a => ofPredicate n L (tri a) hL (ht a)) P)
    (triples : ∀ p∈P, (supports n L p).card=3)
    (rigid : ∀ p∈P,
      (ordinaryDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) p=2 ∧
       coreDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) p=2) ∨
      (ordinaryDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) p=0 ∧
       coreDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) p=6)) : False := by
  classical
  let G := fun a => ofPredicate n L (tri a) hL (ht a)
  let R := P.filter (fun p => ordinaryDegree n L G p=2)
  have norm (c : Point) (hc : c∈R) : ∃ f : UpperFan.Sectors n 3 L,
      f.center=c ∧ NormalizedData G f := by
    obtain ⟨hcP,hca⟩ := mem_filter.mp hc
    have hcd : coreDegree n L G c=2 := by
      have h := rigid c hcP
      change (ordinaryDegree n L G c=2 ∧ coreDegree n L G c=2) ∨
        (ordinaryDegree n L G c=0 ∧ coreDegree n L G c=6) at h
      rcases h with h|h
      · exact h.2
      · omega
    apply UpperOpenMathHighNeighborCharts.certificate_high_neighbor_normalized_chart
      n L hL hn tri hi ht c (sub hcP) (triples c hcP) hca hcd
    intro d hd edge
    have hdP : d∈P := closed {c,d} edge c (by simp) hcP (by simp)
    refine ⟨triples d hdP,?_⟩
    change 3≤ordinaryDegree n L G d+coreDegree n L G d
    have h := rigid d hdP
    change (ordinaryDegree n L G d=2 ∧ coreDegree n L G d=2) ∨
      (ordinaryDegree n L G d=0 ∧ coreDegree n L G d=6) at h
    rcases h with h|h <;> omega
  have rclosed : SharedCoreClosed n L G R := by
    intro e he c hce hcR d hde
    have hcP := (mem_filter.mp hcR).1
    have hdP : d∈P := closed e he c hce hcP hde
    by_cases hdc : d=c
    · simpa only [hdc] using hcR
    have pair : e={c,d} := by
      apply Eq.symm
      apply eq_of_subset_of_card_le
      · intro x hx
        rcases mem_insert.mp hx with rfl|hx
        · exact hce
        · simpa only [mem_singleton.mp hx] using hde
      · rw [card_pair (fun h => hdc h.symm),used_edge_card G (mem_filter.mp (mem_sdiff.mp he).1).1]
    rcases rigid d hdP with hd|hd
    · exact mem_filter.mpr ⟨hdP,hd.1⟩
    · obtain ⟨f,fc,df⟩ := norm c hcR
      have full : coreDegree n L G d=2*(supports n L d).card := by rw [hd.2,triples d hdP]
      exact False.elim (certificate_normalized_full_not_adjacent n L hL hn tri hi ht f df d
        (sub hdP) full (by simpa only [fc,pair] using he))
  by_cases rnonempty : R.Nonempty
  · apply UpperOpenMathTwoTwoCore.certificate_closed_two_two_impossible
      n L hL hn tri hi ht R ((filter_subset _ _).trans sub) rnonempty rclosed
    intro c hc
    obtain ⟨hcP,hca⟩ := mem_filter.mp hc
    refine ⟨triples c hcP,hca,?_⟩
    rcases rigid c hcP with h|h
    · exact h.2
    · have hzero : ordinaryDegree n L G c=0 := h.1
      omega
  · have rempty : R=∅ := not_nonempty_iff_eq_empty.mp rnonempty
    apply UpperOpenMathFullCoreFans.certificate_closed_full_core_impossible
      n L hL hn tri hi ht P sub nonempty closed
    intro c hc
    rcases rigid c hc with h|h
    · have hm : c∈R := mem_filter.mpr ⟨hc,h.1⟩
      rw [rempty] at hm
      exact False.elim (notMem_empty c hm)
    · rw [h.2,triples c hc]

#print axioms normalized_full_incompatible
#print axioms certificate_normalized_full_not_adjacent
#print axioms certificate_closed_zero_types_impossible
end Kobon.UpperOpenMathTripleZeroCurvature
