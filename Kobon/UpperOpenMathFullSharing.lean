import Kobon.UpperOpenMathFullCoreFans

/-! Full shared fans, including ordinary tips, surround their centers by
actual core neighbors. The penultimate shared degree is impossible at any
multiplicity, so an exposed core loses at least two shared rays. -/
namespace Kobon.UpperOpenMathFullSharing
open Cells FanGeometry UpperFan UpperVertexBudget UpperTriangleIncidence
  UpperSharedIncidence UpperCoreExtraction UpperOpenMathRadialOrder
  UpperOpenMathActualFans UpperOpenMathCapHeavyTriples UpperOpenMathCoreComponents Finset
set_option maxHeartbeats 1000000

theorem shared_full {n r : ℕ} [NeZero (2*r)] {L : ℕ → Line ℝ}
    (f : UpperFan.Sectors n r L) (hs : f.shared.card=2*r) : f.triangular=univ := by
  classical
  apply eq_of_subset_of_card_le (subset_univ _)
  have ge := card_le_card (filter_subset (fun z => z-1∈f.triangular) f.triangular)
  change f.shared.card≤f.triangular.card at ge
  simpa only [card_univ,ZMod.card] using hs.ge.trans ge

theorem shared_gap {n r : ℕ} [NeZero (2*r)] {L : ℕ → Line ℝ}
    (hr : 1≤r) (f : UpperFan.Sectors n r L) :
    f.shared.card=2*r ∨ f.shared.card≤2*r-2 := by
  classical
  by_cases hall : f.triangular=univ
  · left
    simp [Sectors.shared,hall]
  · right
    have missing : ∃ z : ZMod (2*r), z∉f.triangular := by
      by_contra h
      push_neg at h
      exact hall (eq_univ_of_forall h)
    obtain ⟨z,hz⟩ := missing
    have ne : z≠z+1 := by
      intro he
      have hone : (0 : ZMod (2*r))=1 := by
        apply add_left_cancel (a:=z)
        simpa only [add_zero] using he
      have hv := congrArg ZMod.val hone
      rw [ZMod.val_zero,ZMod.val_one'' (by omega : 2*r≠1)] at hv
      omega
    have h0 : z∉f.shared := fun h => hz (mem_filter.mp h).1
    have h1 : z+1∉f.shared := by
      intro h
      have hh := (mem_filter.mp h).2
      exact hz (by simpa using hh)
    have sub : ({z,z+1} : Finset (ZMod (2*r)))⊆univ\f.shared := by
      intro x hx
      rcases mem_insert.mp hx with rfl|hx
      · exact mem_sdiff.mpr ⟨mem_univ _,h0⟩
      · have he := mem_singleton.mp hx
        subst x
        exact mem_sdiff.mpr ⟨mem_univ _,h1⟩
    have bound := card_le_card sub
    have total := card_sdiff_add_card_eq_card (subset_univ f.shared)
    rw [card_pair ne] at bound
    simp only [card_univ,ZMod.card] at total
    omega

theorem certificate_full_sharing_neighbors_surround {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (c : Point) (hc : c∈core n L) (w : Line ℝ)
    (hw : affineEval w c=0) (valid : w.a≠0 ∨ w.b≠0)
    (full : ordinaryDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) c+
      coreDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) c=2*(supports n L c).card) :
    ∃ q∈core n L, {c,q}∈twoCoreEdges n L (fun a => ofPredicate n L (tri a) hL (ht a)) ∧
      affineEval w q<0 := by
  classical
  have hr := core_multiplicity n L hL hc
  letI : NeZero (2*(supports n L c).card) := ⟨by omega⟩
  let D := atPoint n L hL hn c
  let f := fan n L hL hn tri ht c (mem_filter.mp hc).1 D (by omega)
  have hfull : f.shared.card=2*(supports n L c).card := by
    rw [← f.shared_card_split,fan_ordinary_card n L hL hn tri ht c (mem_filter.mp hc).1 D (by omega) hi hc,
      fan_core_card n L hL hn tri ht c (mem_filter.mp hc).1 D (by omega) hi hc]
    exact full
  have hall := shared_full f hfull
  obtain ⟨z,noOrd,negative⟩ := UpperFanSupport.Sectors.exists_negative_core_endpoint
    f hall (fan_positive n L hL hn tri ht c (mem_filter.mp hc).1 D (by omega)) w hw valid
  have hz : z∈f.coreShared := mem_sdiff.mpr ⟨by simp [Sectors.shared,hall],by
    intro h
    exact noOrd ((f.mem_ordinaryShared z).mp h).2.2⟩
  exact ⟨f.point z,fan_core_endpoint n L hL hn tri ht c (mem_filter.mp hc).1 D (by omega) hi hc z hz,
    (fan_core_iff n L hL hn tri ht c (mem_filter.mp hc).1 D (by omega) hi hc z).mp hz,negative⟩

theorem certificate_supported_sharing_gap {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (c : Point) (hc : c∈core n L) (w : Line ℝ)
    (hw : affineEval w c=0) (valid : w.a≠0 ∨ w.b≠0)
    (support : ∀ q∈core n L, 0≤affineEval w q) :
    ordinaryDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) c+
      coreDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) c≤2*(supports n L c).card-2 := by
  classical
  have hr := core_multiplicity n L hL hc
  letI : NeZero (2*(supports n L c).card) := ⟨by omega⟩
  let D := atPoint n L hL hn c
  let f := fan n L hL hn tri ht c (mem_filter.mp hc).1 D (by omega)
  have gap := shared_gap (by omega : 1≤(supports n L c).card) f
  rw [← f.shared_card_split,fan_ordinary_card n L hL hn tri ht c (mem_filter.mp hc).1 D (by omega) hi hc,
    fan_core_card n L hL hn tri ht c (mem_filter.mp hc).1 D (by omega) hi hc] at gap
  rcases gap with full|less
  · obtain ⟨q,hq,_,neg⟩ := certificate_full_sharing_neighbors_surround n L hL hn tri hi ht c hc w hw valid full
    exact False.elim (not_lt_of_ge (support q hq) neg)
  · exact less

#print axioms shared_gap
#print axioms certificate_full_sharing_neighbors_surround
#print axioms certificate_supported_sharing_gap
end Kobon.UpperOpenMathFullSharing
