import Kobon.UpperOpenMathClosedTwoCapCharts
import Kobon.UpperOpenMathNormalizedPairFullSwap
import Kobon.UpperOpenMathNormalizedFullNeighbors
import Kobon.UpperOpenMathClosedFullSharing

/-! Balanced and full two-cap triple cores cannot form a closed zero-cost
component. This geometric equality obstruction does not restrict its size. -/
namespace Kobon.UpperOpenMathTwoCapNeighborRigidity
open Cells FanGeometry UpperFan UpperVertexBudget UpperTriangleIncidence UpperSharedIncidence
  UpperCoreExtraction UpperOpenMathCapHeavyTriples UpperOpenMathCoreComponents
  UpperOpenMathActualFans UpperOpenMathTripleCharts UpperOpenMathTwoTwoCore Finset
set_option maxHeartbeats 1000000

theorem core_image_degree {α : Type*} [Fintype α] (G : α → TriangleGeometry)
    {n : ℕ} {L : ℕ → Line ℝ} (f : UpperFan.Sectors n 3 L)
    (inj : Function.Injective f.point) (nc : ∀ z, f.point z≠f.center)
    (im : f.coreShared.image (fun z => ({f.center,f.point z} : Edge))=
      (twoCoreEdges n L G).filter (fun e => f.center∈e)) :
    f.coreShared.card=coreDegree n L G f.center := by
  classical
  have hh := congrArg Finset.card im
  rw [card_image_of_injective _ (pair_map_injective f.center f.point inj nc)] at hh
  exact hh

theorem normalized_two_or_full_neighbors_no_full {α : Type*} [Fintype α]
    (G : α → TriangleGeometry)
    (disjoint : Pairwise (fun a b => Disjoint (G a).interior (G b).interior))
    {n : ℕ} {L : ℕ → Line ℝ} (hL : NoParallel n L)
    (f g k : UpperFan.Sectors n 3 L) (df : NormalizedData G f)
    (dg : NormalizedData G g ∨ UpperOpenMathAntipodalTwoCapChart.AntipodalData G g)
    (dk : NormalizedData G k ∨ UpperOpenMathAntipodalTwoCapChart.AntipodalData G k)
    (w x : ZMod (2*3)) (gw : w∈g.coreShared) (kx : x∈k.coreShared)
    (gc : g.center=f.point 1) (gp : g.point w=f.center)
    (kc : k.center=f.point 2) (kp : k.point x=f.center)
    (full : g.coreShared.card=4 ∨ k.coreShared.card=4) : False := by
  classical
  have f1 : (1 : ZMod (2*3))∈f.coreShared := by rw [df.core_eq]; simp
  have f2 : (2 : ZMod (2*3))∈f.coreShared := by rw [df.core_eq]; simp
  rcases dg with dg|dg <;> rcases dk with dk|dk
  · have gg := dg.core_card
    have kk := dk.core_card
    omega
  · exact UpperOpenMathNormalizedPairFull.normalized_pair_full_third_impossible
      G disjoint hL f g k df dg dk.injective dk.noncentral dk.positive dk.occurrences
      dk.triangular_eq w x gw kx gc gp kc kp
  · exact UpperOpenMathNormalizedPairFullSwap.normalized_swapped_pair_full_third_impossible
      G disjoint hL f k g df dk dg.injective dg.noncentral dg.positive dg.occurrences
      dg.triangular_eq x w kx gw kc kp gc gp
  · have fg := UpperOpenMathNormalizedPairFull.retained_matching_general G disjoint
      (by decide : 2≤3) f g df.toChartData dg.injective dg.noncentral dg.positive dg.occurrences
      1 w f1 gw gc gp
    have fk := UpperOpenMathNormalizedPairFull.retained_matching_general G disjoint
      (by decide : 2≤3) f k df.toChartData dk.injective dk.noncentral dk.positive dk.occurrences
      2 x f2 kx kc kp
    have h11 : (1 : ZMod (2*3))-1=0 := by decide
    have h12 : (1 : ZMod (2*3))+1=2 := by decide
    have h21 : (2 : ZMod (2*3))-1=1 := by decide
    have h23 : (2 : ZMod (2*3))+1=3 := by decide
    exact UpperOpenMathNormalizedFullNeighbors.normalized_full_neighbors_impossible G hL
      f g k df dg.triangular_eq dk.triangular_eq dg.noncentral w x gc gp
      (by simpa only [h12] using fg.1) (by simpa only [h11] using fg.2) kc kp
      (by simpa only [h23] using fk.1) (by simpa only [h21] using fk.2)

theorem reverse_label_of_image {α : Type*} [Fintype α] (G : α → TriangleGeometry)
    {n : ℕ} {L : ℕ → Line ℝ} (f : UpperFan.Sectors n 3 L)
    (im : f.coreShared.image (fun z => ({f.center,f.point z} : Edge))=
      (twoCoreEdges n L G).filter (fun e => f.center∈e))
    (p : Point) (ne : p≠f.center) (edge : {f.center,p}∈twoCoreEdges n L G) :
    ∃ z, z∈f.coreShared ∧ f.point z=p := by
  classical
  have hm : ({f.center,p} : Edge)∈(twoCoreEdges n L G).filter (fun e => f.center∈e) :=
    mem_filter.mpr ⟨edge,by simp⟩
  rw [← im] at hm
  obtain ⟨z,hz,he⟩ := mem_image.mp hm
  have hp : p∈({f.center,f.point z} : Edge) := by rw [he]; simp
  rcases mem_insert.mp hp with hp|hp
  · exact False.elim (ne hp)
  · exact ⟨z,hz,(mem_singleton.mp hp).symm⟩

theorem certificate_closed_two_or_four_impossible {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (P : Finset Point) (sub : P⊆core n L) (nonempty : P.Nonempty)
    (closed : SharedCoreClosed n L (fun a => ofPredicate n L (tri a) hL (ht a)) P)
    (rigid : ∀ c∈P, (supports n L c).card=3 ∧
      ordinaryDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) c=2 ∧
      (coreDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) c=2 ∨
       coreDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) c=4)) : False := by
  classical
  let G := fun a => ofPredicate n L (tri a) hL (ht a)
  let R := P.filter (fun p => coreDegree n L G p=2)
  have disjoint : Pairwise (fun a b => Disjoint (G a).interior (G b).interior) := by
    intro a b hab
    exact distinct_interiors_disjoint n L _ _ hL (ht a) (ht b) (fun he => hab (hi he))
  have norm (c : Point) (hc : c∈R) : ∃ f : UpperFan.Sectors n 3 L,
      f.center=c ∧ NormalizedData G f := by
    obtain ⟨hcP,hcd⟩ := mem_filter.mp hc
    have zero := UpperOpenMathClosedTwoCapCharts.certificate_closed_two_cap_zero_marks
      n L hL hn tri hi ht P sub closed (fun p hp => (rigid p hp).1)
      (fun p hp => (rigid p hp).2.1) c hcP
    exact UpperOpenMathMarkedPorts.certificate_normalized_two_two_of_zero_marks
      n L hL hn tri hi ht c (sub hcP) (rigid c hcP).1 (rigid c hcP).2.1 hcd zero
  have rclosed : SharedCoreClosed n L G R := by
    intro e he c hce hcR d hde
    have hcP := (mem_filter.mp hcR).1
    have hdP : d∈P := closed e he c hce hcP hde
    rcases (rigid d hdP).2.2 with hd2|hd4
    · exact mem_filter.mpr ⟨hdP,hd2⟩
    · by_cases hdc : d=c
      · have hc2 := (mem_filter.mp hcR).2
        change coreDegree n L G c=2 at hc2
        rw [hdc] at hd4
        change coreDegree n L G c=4 at hd4
        omega
      have pair : e={c,d} := by
        apply Eq.symm
        apply eq_of_subset_of_card_le
        · intro p hp
          rcases mem_insert.mp hp with rfl|hp
          · exact hce
          · simpa only [mem_singleton.mp hp] using hde
        · rw [card_pair (fun h => hdc h.symm),used_edge_card G (mem_filter.mp (mem_sdiff.mp he).1).1]
      obtain ⟨f,fc,df⟩ := norm c hcR
      have f1 : (1 : ZMod (2*3))∈f.coreShared := by rw [df.core_eq]; simp
      have f2 : (2 : ZMod (2*3))∈f.coreShared := by rw [df.core_eq]; simp
      have fpP (z : ZMod (2*3)) (hz : z∈f.coreShared) : f.point z∈P :=
        closed {f.center,f.point z} (core_edge_of_label G f df.toChartData z hz)
          f.center (by simp) (by simpa only [fc] using hcP) (by simp)
      obtain ⟨g,gc,dg⟩ := UpperOpenMathClosedTwoCapCharts.certificate_closed_two_or_four_chart
        n L hL hn tri hi ht P sub closed rigid (f.point 1) (fpP 1 f1)
      obtain ⟨k,kc,dk⟩ := UpperOpenMathClosedTwoCapCharts.certificate_closed_two_or_four_chart
        n L hL hn tri hi ht P sub closed rigid (f.point 2) (fpP 2 f2)
      have gi : Function.Injective g.point := by rcases dg with h|h <;> exact h.injective
      have gn : ∀ z, g.point z≠g.center := by rcases dg with h|h <;> exact h.noncentral
      have gm : g.coreShared.image (fun z => ({g.center,g.point z} : Edge))=
          (twoCoreEdges n L G).filter (fun e => g.center∈e) := by
        rcases dg with h|h <;> exact h.core_image
      have ki : Function.Injective k.point := by rcases dk with h|h <;> exact h.injective
      have kn : ∀ z, k.point z≠k.center := by rcases dk with h|h <;> exact h.noncentral
      have km : k.coreShared.image (fun z => ({k.center,k.point z} : Edge))=
          (twoCoreEdges n L G).filter (fun e => k.center∈e) := by
        rcases dk with h|h <;> exact h.core_image
      obtain ⟨w,gw,gp⟩ := reverse_label_of_image G g gm f.center
        (by rw [gc]; exact (df.noncentral 1).symm)
        (by simpa only [gc,pair_comm] using core_edge_of_label G f df.toChartData 1 f1)
      obtain ⟨x,kx,kp⟩ := reverse_label_of_image G k km f.center
        (by rw [kc]; exact (df.noncentral 2).symm)
        (by simpa only [kc,pair_comm] using core_edge_of_label G f df.toChartData 2 f2)
      obtain ⟨z,fz,fd⟩ := reverse_core_label G f df.toChartData d
        (by simpa only [fc] using hdc)
        (by simpa only [fc,pair] using he)
      have cases : z=1 ∨ z=2 := by simpa only [df.core_eq,mem_insert,mem_singleton] using fz
      have full : g.coreShared.card=4 ∨ k.coreShared.card=4 := by
        rcases cases with rfl|rfl
        · left
          rw [core_image_degree G g gi gn gm,gc,fd]
          exact hd4
        · right
          rw [core_image_degree G k ki kn km,kc,fd]
          exact hd4
      exact False.elim (normalized_two_or_full_neighbors_no_full G disjoint hL f g k df dg dk
        w x gw kx gc gp kc kp full)
  by_cases rnonempty : R.Nonempty
  · apply certificate_closed_two_two_impossible n L hL hn tri hi ht R
      ((filter_subset _ _).trans sub) rnonempty rclosed
    intro c hc
    obtain ⟨hcP,hcd⟩ := mem_filter.mp hc
    exact ⟨(rigid c hcP).1,(rigid c hcP).2.1,hcd⟩
  · have rempty : R=∅ := not_nonempty_iff_eq_empty.mp rnonempty
    apply UpperOpenMathClosedFullSharing.certificate_closed_full_sharing_impossible
      n L hL hn tri hi ht P sub nonempty closed
    intro c hc
    obtain ⟨rc,ac,dc⟩ := rigid c hc
    have hd4 : coreDegree n L G c=4 := by
      rcases dc with dc|dc
      · have hm : c∈R := mem_filter.mpr ⟨hc,dc⟩
        rw [rempty] at hm
        exact False.elim (notMem_empty c hm)
      · exact dc
    rw [ac,hd4,rc]

#print axioms normalized_two_or_full_neighbors_no_full
#print axioms certificate_closed_two_or_four_impossible
end Kobon.UpperOpenMathTwoCapNeighborRigidity
