import Kobon.UpperOpenMathSharedRays
import Kobon.UpperCoreCombinatorics

/-!
# Fully extracted local core fans and actual incidence cardinalities

The actual shared edges incident to a core are in bijection with the shared
canonical rays of its selected triangular sectors. Ordinary/core endpoint
classification gives the corresponding D1/D2 bijections. The final local
fan bounds therefore concern actual arrangements and actual certified
triangle families, with no ordering, extraction or counting premise.
-/
namespace Kobon.UpperOpenMathActualFans
open Cells FanGeometry UpperVertexBudget UpperEdgeInventory UpperTriangleIncidence
  UpperSharedIncidence UpperCoreExtraction UpperOpenMathRadialOrder
  UpperOpenMathSectorRecords UpperOpenMathSectorIncidence Finset

theorem pair_of_card_two_of_mem {α : Type*} [DecidableEq α]
    (e : Finset α) (c : α) (hc : c∈e) (he : e.card=2) :
    ∃ q : α, q≠c ∧ e={c,q} := by
  obtain ⟨a,b,hab,hpair⟩ := card_eq_two.mp he
  rw [hpair] at hc
  simp only [mem_insert,mem_singleton] at hc
  rcases hc with rfl|rfl
  · exact ⟨b,hab.symm,hpair⟩
  · exact ⟨a,hab,by simpa only [pair_comm] using hpair⟩

theorem pair_map_injective {r : ℕ} [NeZero (2*r)] (c : Point)
    (P : ZMod (2*r) → Point) (pinj : Function.Injective P) (pne : ∀ z, P z≠c) :
    Function.Injective (fun z => ({c,P z} : Edge)) := by
  classical
  intro a b he
  change ({c,P a} : Edge)={c,P b} at he
  have hm : P a∈({c,P b} : Edge) := by rw [← he]; simp
  have hp : P a=P b := by simpa only [mem_insert,mem_singleton,or_iff_right (pne a)] using hm
  exact pinj hp

section Chart
variable {α : Type*} [Fintype α]
  (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
  (tri : α → Triple) (ht : ∀ a, TrianglePredicate n L (tri a))
  (c : Point) (hc : c∈vertices n L)
  (D : OrderedDirections n L (supports n L c))
  [NeZero (2*(supports n L c).card)] (hcard : 2≤(supports n L c).card)

noncomputable def fan : UpperFan.Sectors n (supports n L c).card L :=
  sectors (fun a => ofPredicate n L (tri a) hL (ht a))
    (fun a => predicate_indexed n L (tri a) hL (ht a)) c
    (D.rayPoint hL hn c hc (fun i hi => (mem_filter.mp hi).2))
    (by omega) D.cyclicRadial
    (fun z => (mem_filter.mp (D.cyclicRadial_mem z)).2)
    (D.rayPoint_on_line hL hn c hc (fun i hi => (mem_filter.mp hi).2))
    (D.rayPoint_antipodal hL hn hcard c hc (fun i hi => (mem_filter.mp hi).2))

theorem fan_positive (z : ZMod (2*(supports n L c).card)) :
    0<areaDet (fan n L hL hn tri ht c hc D hcard).center
      ((fan n L hL hn tri ht c hc D hcard).point z)
      ((fan n L hL hn tri ht c hc D hcard).point (z+1)) :=
  D.rayPoint_positive_orientation hL hn hcard c hc (fun i hi => (mem_filter.mp hi).2) z

theorem fan_point_injective : Function.Injective (fan n L hL hn tri ht c hc D hcard).point :=
  D.rayPoint_injective hL hn hcard c hc (fun i hi => (mem_filter.mp hi).2)

theorem fan_point_ne_center (z : ZMod (2*(supports n L c).card)) :
    (fan n L hL hn tri ht c hc D hcard).point z≠c :=
  D.cyclicPoint_ne_center c z _ (D.rayScale_positive hL hn c hc (fun i hi => (mem_filter.mp hi).2) z)

theorem fan_shared_iff (hi : Function.Injective tri)
    (z : ZMod (2*(supports n L c).card)) :
    z∈(fan n L hL hn tri ht c hc D hcard).shared ↔
      {c,(fan n L hL hn tri ht c hc D hcard).point z}∈
        sharedEdges (fun a => ofPredicate n L (tri a) hL (ht a)) := by
  change z∈(triangular (fun a => ofPredicate n L (tri a) hL (ht a)) c
    (D.rayPoint hL hn c hc (fun i hi => (mem_filter.mp hi).2))).filter
      (fun z => z-1∈triangular (fun a => ofPredicate n L (tri a) hL (ht a)) c
        (D.rayPoint hL hn c hc (fun i hi => (mem_filter.mp hi).2))) ↔ _
  rw [mem_filter]
  exact (UpperOpenMathSharedRays.certificate_shared_ray_iff n L hL hn tri hi ht c hc D hcard z).symm

theorem fan_ordinary_iff (hi : Function.Injective tri) (hcore : c∈core n L)
    (z : ZMod (2*(supports n L c).card)) :
    z∈(fan n L hL hn tri ht c hc D hcard).ordinaryShared ↔
      {c,(fan n L hL hn tri ht c hc D hcard).point z}∈
        oneCoreEdges n L (fun a => ofPredicate n L (tri a) hL (ht a)) := by
  classical
  let f := fan n L hL hn tri ht c hc D hcard
  have hcno := (mem_filter.mp hcore).2
  change z∈f.ordinaryShared ↔
    {c,f.point z}∈oneCoreEdges n L (fun a => ofPredicate n L (tri a) hL (ht a))
  simp only [UpperFan.Sectors.ordinaryShared,oneCoreEdges,mem_filter]
  rw [fan_shared_iff n L hL hn tri ht c hc D hcard hi]
  constructor
  · rintro ⟨hs,ho⟩
    exact ⟨hs,f.point z,by simp,ho⟩
  · rintro ⟨hs,p,hp,ho⟩
    simp only [mem_insert,mem_singleton] at hp
    rcases hp with rfl|rfl
    · exact False.elim (hcno ho)
    · exact ⟨hs,ho⟩

theorem fan_core_iff (hi : Function.Injective tri) (hcore : c∈core n L)
    (z : ZMod (2*(supports n L c).card)) :
    z∈(fan n L hL hn tri ht c hc D hcard).coreShared ↔
      {c,(fan n L hL hn tri ht c hc D hcard).point z}∈
        twoCoreEdges n L (fun a => ofPredicate n L (tri a) hL (ht a)) := by
  classical
  simp only [UpperFan.Sectors.coreShared,twoCoreEdges,mem_sdiff,
    fan_shared_iff n L hL hn tri ht c hc D hcard hi,
    fan_ordinary_iff n L hL hn tri ht c hc D hcard hi hcore]

theorem fan_ordinary_image (hi : Function.Injective tri) (hcore : c∈core n L) :
    ((fan n L hL hn tri ht c hc D hcard).ordinaryShared.image
      (fun z => {c,(fan n L hL hn tri ht c hc D hcard).point z}))=
    (oneCoreEdges n L (fun a => ofPredicate n L (tri a) hL (ht a))).filter (fun e => c∈e) := by
  classical
  let f := fan n L hL hn tri ht c hc D hcard
  let G := fun a => ofPredicate n L (tri a) hL (ht a)
  ext e
  constructor
  · intro he
    obtain ⟨z,hz,rfl⟩ := mem_image.mp he
    exact mem_filter.mpr ⟨(fan_ordinary_iff n L hL hn tri ht c hc D hcard hi hcore z).mp hz,by simp⟩
  · intro he
    obtain ⟨he,hce⟩ := mem_filter.mp he
    have hused := (mem_filter.mp (mem_filter.mp he).1).1
    obtain ⟨q,hqc,heq⟩ := pair_of_card_two_of_mem e c hce (used_edge_card G hused)
    have hpair : {c,q}∈usedEdges G := by simpa only [heq] using hused
    obtain ⟨z,hz⟩ := used_edge_has_ray n L hL hn tri ht c hc D q hqc hpair
    change f.point z=q at hz
    have hez : {c,f.point z}=e := by rw [hz]; exact heq.symm
    exact mem_image.mpr ⟨z,(fan_ordinary_iff n L hL hn tri ht c hc D hcard hi hcore z).mpr
      (by rw [hez]; exact he),hez⟩

theorem fan_core_image (hi : Function.Injective tri) (hcore : c∈core n L) :
    ((fan n L hL hn tri ht c hc D hcard).coreShared.image
      (fun z => {c,(fan n L hL hn tri ht c hc D hcard).point z}))=
    (twoCoreEdges n L (fun a => ofPredicate n L (tri a) hL (ht a))).filter (fun e => c∈e) := by
  classical
  let f := fan n L hL hn tri ht c hc D hcard
  let G := fun a => ofPredicate n L (tri a) hL (ht a)
  ext e
  constructor
  · intro he
    obtain ⟨z,hz,rfl⟩ := mem_image.mp he
    exact mem_filter.mpr ⟨(fan_core_iff n L hL hn tri ht c hc D hcard hi hcore z).mp hz,by simp⟩
  · intro he
    obtain ⟨he,hce⟩ := mem_filter.mp he
    have hused := (mem_filter.mp (mem_sdiff.mp he).1).1
    obtain ⟨q,hqc,heq⟩ := pair_of_card_two_of_mem e c hce (used_edge_card G hused)
    have hpair : {c,q}∈usedEdges G := by simpa only [heq] using hused
    obtain ⟨z,hz⟩ := used_edge_has_ray n L hL hn tri ht c hc D q hqc hpair
    change f.point z=q at hz
    have hez : {c,f.point z}=e := by rw [hz]; exact heq.symm
    exact mem_image.mpr ⟨z,(fan_core_iff n L hL hn tri ht c hc D hcard hi hcore z).mpr
      (by rw [hez]; exact he),hez⟩

theorem fan_ordinary_card (hi : Function.Injective tri) (hcore : c∈core n L) :
    (fan n L hL hn tri ht c hc D hcard).ordinaryShared.card=
      ((oneCoreEdges n L (fun a => ofPredicate n L (tri a) hL (ht a))).filter (fun e => c∈e)).card := by
  classical
  rw [← fan_ordinary_image n L hL hn tri ht c hc D hcard hi hcore,
    card_image_of_injective _ (pair_map_injective c _
      (fan_point_injective n L hL hn tri ht c hc D hcard)
      (fan_point_ne_center n L hL hn tri ht c hc D hcard))]

theorem fan_core_card (hi : Function.Injective tri) (hcore : c∈core n L) :
    (fan n L hL hn tri ht c hc D hcard).coreShared.card=
      ((twoCoreEdges n L (fun a => ofPredicate n L (tri a) hL (ht a))).filter (fun e => c∈e)).card := by
  classical
  rw [← fan_core_image n L hL hn tri ht c hc D hcard hi hcore,
    card_image_of_injective _ (pair_map_injective c _
      (fan_point_injective n L hL hn tri ht c hc D hcard)
      (fan_point_ne_center n L hL hn tri ht c hc D hcard))]

theorem fan_core_endpoint (hi : Function.Injective tri) (hcore : c∈core n L)
    (z : ZMod (2*(supports n L c).card))
    (hz : z∈(fan n L hL hn tri ht c hc D hcard).coreShared) :
    (fan n L hL hn tri ht c hc D hcard).point z∈core n L := by
  classical
  let f := fan n L hL hn tri ht c hc D hcard
  let G := fun a => ofPredicate n L (tri a) hL (ht a)
  have he := (fan_core_iff n L hL hn tri ht c hc D hcard hi hcore z).mp hz
  have hused := (mem_filter.mp (mem_sdiff.mp he).1).1
  exact mem_filter.mpr ⟨certificate_side_vertices n L hL tri ht hused (by simp),
    twoCore_endpoints n L G he _ (by simp)⟩

end Chart

section LocalBounds
variable {α : Type*} [Fintype α]
  (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
  (tri : α → Triple) (hi : Function.Injective tri)
  (ht : ∀ a, TrianglePredicate n L (tri a)) (c : Point) (hcore : c∈core n L)

include hn hi hcore

theorem certificate_local_fan_bound :
    ((oneCoreEdges n L (fun a => ofPredicate n L (tri a) hL (ht a))).filter (fun e => c∈e)).card≤
      2*(supports n L c).card-3 := by
  classical
  have hr := core_multiplicity n L hL hcore
  letI : NeZero (2*(supports n L c).card) := ⟨by omega⟩
  let D := atPoint n L hL hn c
  have hc := (mem_filter.mp hcore).1
  rw [← fan_ordinary_card n L hL hn tri ht c hc D (by omega) hi hcore]
  exact (fan n L hL hn tri ht c hc D (by omega)).ordinary_shared_card_le hr

theorem certificate_local_weighted_bound :
    3*((oneCoreEdges n L (fun a => ofPredicate n L (tri a) hL (ht a))).filter (fun e => c∈e)).card+
      ((twoCoreEdges n L (fun a => ofPredicate n L (tri a) hL (ht a))).filter (fun e => c∈e)).card≤
      6*(supports n L c).card-8+
        (if ((oneCoreEdges n L (fun a => ofPredicate n L (tri a) hL (ht a))).filter (fun e => c∈e)).card=
          2*(supports n L c).card-3 then 2 else 0) := by
  classical
  have hr := core_multiplicity n L hL hcore
  letI : NeZero (2*(supports n L c).card) := ⟨by omega⟩
  let D := atPoint n L hL hn c
  have hc := (mem_filter.mp hcore).1
  rw [← fan_ordinary_card n L hL hn tri ht c hc D (by omega) hi hcore,
    ← fan_core_card n L hL hn tri ht c hc D (by omega) hi hcore]
  exact (fan n L hL hn tri ht c hc D (by omega)).weighted_local_bound hr

theorem certificate_local_core_degree :
    ((twoCoreEdges n L (fun a => ofPredicate n L (tri a) hL (ht a))).filter (fun e => c∈e)).card≤
      (core n L).card-1 := by
  classical
  have hr := core_multiplicity n L hL hcore
  letI : NeZero (2*(supports n L c).card) := ⟨by omega⟩
  let D := atPoint n L hL hn c
  have hc := (mem_filter.mp hcore).1
  let f := fan n L hL hn tri ht c hc D (by omega)
  have hsub : f.coreShared.image f.point⊆(core n L).erase c := by
    intro p hp
    obtain ⟨z,hz,rfl⟩ := mem_image.mp hp
    exact mem_erase.mpr ⟨fan_point_ne_center n L hL hn tri ht c hc D (by omega) z,
      fan_core_endpoint n L hL hn tri ht c hc D (by omega) hi hcore z hz⟩
  have hcard := card_le_card hsub
  rw [card_image_of_injective _ (fan_point_injective n L hL hn tri ht c hc D (by omega)),
    card_erase_of_mem hcore,fan_core_card n L hL hn tri ht c hc D (by omega) hi hcore] at hcard
  exact hcard

theorem certificate_local_fan_bound_small_core (hsmall : (core n L).card≤3) :
    ((oneCoreEdges n L (fun a => ofPredicate n L (tri a) hL (ht a))).filter (fun e => c∈e)).card≤
      2*(supports n L c).card-4 := by
  classical
  have hr := core_multiplicity n L hL hcore
  letI : NeZero (2*(supports n L c).card) := ⟨by omega⟩
  let D := atPoint n L hL hn c
  have hc := (mem_filter.mp hcore).1
  have hd := certificate_local_core_degree n L hL hn tri hi ht c hcore
  rw [← fan_ordinary_card n L hL hn tri ht c hc D (by omega) hi hcore]
  apply (fan n L hL hn tri ht c hc D (by omega)).ordinary_shared_card_le_of_core_le_two hr
  rw [fan_core_card n L hL hn tri ht c hc D (by omega) hi hcore]
  omega

end LocalBounds

#print axioms fan_ordinary_card
#print axioms fan_core_card
#print axioms certificate_local_fan_bound
#print axioms certificate_local_weighted_bound
#print axioms certificate_local_fan_bound_small_core
end Kobon.UpperOpenMathActualFans
