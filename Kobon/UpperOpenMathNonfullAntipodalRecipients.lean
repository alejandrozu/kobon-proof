import Kobon.UpperOpenMathOneCapThreeCoreDegree

/-! Every nonfull triple recipient has at most two antipodal full neighbors.
In particular the zero-cap degree-four recipient uses at most two slots. -/
namespace Kobon.UpperOpenMathNonfullAntipodalRecipients
open Cells FanGeometry UpperFan UpperVertexBudget UpperTriangleIncidence
  UpperSharedIncidence UpperCoreExtraction UpperOpenMathRadialOrder
  UpperOpenMathSectorRecords UpperOpenMathActualFans UpperOpenMathCapHeavyTriples
  UpperOpenMathAntipodalAdjacency UpperOpenMathUnmarkedCrossResources Finset
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem finite_selected_adjacent : ∀ T C : Finset (ZMod 6),
    C⊆T.filter (fun z=>z-1∈T) → 3≤C.card →
    (T.filter (fun z=>z-1∈T)).card≤4 → ∃ z∈C, z+1∈C := by
  decide +kernel

theorem selected_adjacent {n r : ℕ} [NeZero (2*r)] {L : ℕ → Line ℝ}
    (f : Sectors n r L) (hr : r=3) (X : Finset (ZMod (2*r)))
    (sub : X⊆f.shared) (hx : 3≤X.card) (hs : f.shared.card≤4) :
    ∃ z∈X, z+1∈X := by
  subst r
  exact finite_selected_adjacent f.triangular X sub hx hs

theorem certificate_nonfull_anti_degree_le_two {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (triples : ∀ c∈core n L, (supports n L c).card=3)
    (c : Point) (hc : c∈core n L)
    (nonfull : ordinaryDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) c+
      coreDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) c≤4) :
    degreeFrom n L (fun a => ofPredicate n L (tri a) hL (ht a))
      (unmarkedFullTwoCapSet n L hL hn tri ht) c≤2 := by
  classical
  let G := fun a => ofPredicate n L (tri a) hL (ht a)
  let A := unmarkedFullTwoCapSet n L hL hn tri ht
  change ordinaryDegree n L G c+coreDegree n L G c≤4 at nonfull
  have rc := triples c hc
  letI : NeZero (2*(supports n L c).card) := ⟨by omega⟩
  let D := atPoint n L hL hn c
  let f := fan n L hL hn tri ht c (mem_filter.mp hc).1 D (by omega)
  let X := f.coreShared.filter fun z=>f.point z∈A
  have sc : f.shared.card≤4 := by
    rw [← f.shared_card_split,
      fan_ordinary_card n L hL hn tri ht c (mem_filter.mp hc).1 D (by omega) hi hc,
      fan_core_card n L hL hn tri ht c (mem_filter.mp hc).1 D (by omega) hi hc]
    exact nonfull
  have cn : c∉A := by
    intro h
    obtain ⟨_,ac,dc,_⟩ := mem_filter.mp h
    change ordinaryDegree n L G c=2 at ac
    change coreDegree n L G c=4 at dc
    omega
  have bound : X.card≤2 := by
    by_contra h
    have sub : X⊆f.shared := (filter_subset _ _).trans sdiff_subset
    obtain ⟨z,hz,hnz⟩ := selected_adjacent f rc X sub (by omega) sc
    obtain ⟨hzC,qa⟩ := mem_filter.mp hz
    obtain ⟨hnzC,ra⟩ := mem_filter.mp hnz
    have zT : z∈f.triangular := (mem_filter.mp (mem_sdiff.mp hzC).1).1
    obtain ⟨o⟩ := (mem_triangular G c f.point z).mp zT
    have cap := transported_side_used G o.index o.triangle o.transport 1
    change ({o.triangle.q,o.triangle.r} : Edge)∈usedEdges G at cap
    rw [o.left,o.right] at cap
    obtain ⟨qCore,qa2,qd4,qm0⟩ := mem_filter.mp qa
    obtain ⟨rCore,ra2,rd4,rm0⟩ := mem_filter.mp ra
    change ordinaryDegree n L G (f.point z)=2 at qa2
    change coreDegree n L G (f.point z)=4 at qd4
    have rq := triples (f.point z) qCore
    have qfull : ordinaryDegree n L G (f.point z)+coreDegree n L G (f.point z)=
        2*(supports n L (f.point z)).card := by omega
    have shared := UpperOpenMathFullCoreSides.certificate_full_core_side_shared
      n L hL hn tri hi ht (f.point z) (f.point (z+1)) qCore rCore cap qfull
    exact certificate_unmarked_full_not_adjacent n L hL hn tri hi ht triples
      (f.point z) (f.point (z+1)) qCore rCore qa2 ra2 qd4 rd4 qm0 rm0 shared
  have imageEq : X.image (fun z=>({c,f.point z} : Edge))=
      (twoCoreEdges n L G).filter (fun e=>c∈e ∧ (e∩A).Nonempty) := by
    ext e
    constructor
    · intro he
      obtain ⟨z,hz,rfl⟩ := mem_image.mp he
      obtain ⟨hzC,hzA⟩ := mem_filter.mp hz
      have he := (fan_core_iff n L hL hn tri ht c (mem_filter.mp hc).1 D (by omega) hi hc z).mp hzC
      exact mem_filter.mpr ⟨he,by simp,⟨f.point z,mem_inter.mpr ⟨by simp,hzA⟩⟩⟩
    · intro he
      obtain ⟨heD,hce,hA⟩ := mem_filter.mp he
      have him : e∈f.coreShared.image (fun z=>({c,f.point z} : Edge)) := by
        rw [fan_core_image n L hL hn tri ht c (mem_filter.mp hc).1 D (by omega) hi hc]
        exact mem_filter.mpr ⟨heD,hce⟩
      obtain ⟨z,hz,rfl⟩ := mem_image.mp him
      obtain ⟨x,hx⟩ := hA
      obtain ⟨hxp,hxA⟩ := mem_inter.mp hx
      have hzA : f.point z∈A := by
        rcases mem_insert.mp hxp with he|he
        · exact False.elim (cn (by simpa only [he] using hxA))
        · simpa only [mem_singleton.mp he] using hxA
      exact mem_image.mpr ⟨z,mem_filter.mpr ⟨hz,hzA⟩,rfl⟩
  have imcard : (X.image (fun z=>({c,f.point z} : Edge))).card=X.card :=
    card_image_of_injective X (pair_map_injective c f.point
      (fan_point_injective n L hL hn tri ht c (mem_filter.mp hc).1 D (by omega))
      (fan_point_ne_center n L hL hn tri ht c (mem_filter.mp hc).1 D (by omega)))
  have eq : degreeFrom n L G A c=X.card := by
    exact (congrArg Finset.card imageEq.symm).trans imcard
  rw [eq]
  exact bound

theorem certificate_zero_cap_four_core_anti_degree_le_two {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (triples : ∀ c∈core n L, (supports n L c).card=3)
    (c : Point) (hc : c∈core n L)
    (ac : ordinaryDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) c=0)
    (dc : coreDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) c=4) :
    degreeFrom n L (fun a => ofPredicate n L (tri a) hL (ht a))
      (unmarkedFullTwoCapSet n L hL hn tri ht) c≤2 :=
  certificate_nonfull_anti_degree_le_two n L hL hn tri hi ht triples c hc (by rw [ac,dc])

#print axioms certificate_nonfull_anti_degree_le_two
#print axioms certificate_zero_cap_four_core_anti_degree_le_two
end Kobon.UpperOpenMathNonfullAntipodalRecipients
