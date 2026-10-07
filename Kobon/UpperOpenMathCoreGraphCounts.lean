import Kobon.UpperOpenMathCoreComponents
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-! The actual shared-core graph has exactly the extracted core degrees
and exactly the extracted two-core edges. -/
namespace Kobon.UpperOpenMathCoreGraphCounts
open Cells FanGeometry UpperVertexBudget UpperTriangleIncidence UpperSharedIncidence
  UpperCoreExtraction UpperOpenMathCapHeavyTriples UpperOpenMathCoreComponents Finset
open scoped BigOperators
set_option maxHeartbeats 800000

noncomputable instance graphAdjDecidable {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (G : α → TriangleGeometry) :
    DecidableRel (coreGraph n L G).Adj := Classical.decRel _

theorem certificate_graph_degree {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L)
    (tri : α → Triple) (ht : ∀ a, TrianglePredicate n L (tri a))
    (p : CoreVertex n L) :
    (coreGraph n L (fun a => ofPredicate n L (tri a) hL (ht a))).degree p=
      coreDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) p.val := by
  classical
  let G := fun a => ofPredicate n L (tri a) hL (ht a)
  let N := (coreGraph n L G).neighborFinset p
  let F := (twoCoreEdges n L G).filter (fun e => p.val∈e)
  have himage : N.image (fun q => ({p.val,q.val} : Edge))=F := by
    ext e
    constructor
    · intro he
      obtain ⟨q,hq,rfl⟩ := mem_image.mp he
      have adj := (SimpleGraph.mem_neighborFinset _ _ _).mp hq
      exact mem_filter.mpr ⟨adj.2,by simp⟩
    · intro he
      obtain ⟨heE,hpe⟩ := mem_filter.mp he
      have hc := used_edge_card G (mem_filter.mp (mem_sdiff.mp heE).1).1
      have hpE : (e.erase p.val).Nonempty := by
        apply card_pos.mp
        rw [card_erase_of_mem hpe,hc]
        omega
      obtain ⟨q,hq⟩ := hpE
      obtain ⟨hqp,hqe⟩ := mem_erase.mp hq
      have hsub := (mem_powersetCard.mp (UpperCoreCombinatorics.core_edge_subset n L hL tri ht heE)).1
      let qq : CoreVertex n L := ⟨q,hsub hqe⟩
      have hpq : p≠qq := by intro hh; exact hqp (congrArg Subtype.val hh).symm
      have epair : e={p.val,q} := by
        apply Eq.symm
        apply eq_of_subset_of_card_le
        · intro x hx
          rcases mem_insert.mp hx with hx|hx
          · simpa only [hx] using hpe
          · simpa only [mem_singleton.mp hx] using hqe
        · rw [card_pair hqp.symm,hc]
      refine mem_image.mpr ⟨qq,?_,epair.symm⟩
      exact (SimpleGraph.mem_neighborFinset _ _ _).mpr ⟨hpq,by simpa only [epair] using heE⟩
  have hinj : Set.InjOn (fun q : CoreVertex n L => ({p.val,q.val} : Edge)) N := by
    intro q hq r hr he
    change ({p.val,q.val} : Edge)={p.val,r.val} at he
    have hqp : q.val≠p.val := by
      intro hh
      exact ((SimpleGraph.mem_neighborFinset _ _ _).mp hq).1 (Subtype.ext hh.symm)
    have hqr : q.val=r.val := by
      have hmem : q.val∈({p.val,r.val} : Edge) := by rw [← he]; simp
      rcases mem_insert.mp hmem with hh|hh
      · exact False.elim (hqp hh)
      · exact mem_singleton.mp hh
    exact Subtype.ext hqr
  have hc := card_image_of_injOn hinj
  rw [himage] at hc
  exact hc.symm

theorem certificate_graph_edge_card {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L)
    (tri : α → Triple) (ht : ∀ a, TrianglePredicate n L (tri a)) :
    (coreGraph n L (fun a => ofPredicate n L (tri a) hL (ht a))).edgeFinset.card=
      (twoCoreEdges n L (fun a => ofPredicate n L (tri a) hL (ht a))).card := by
  classical
  let G := fun a => ofPredicate n L (tri a) hL (ht a)
  change (coreGraph n L G).edgeFinset.card=(twoCoreEdges n L G).card
  have hs := (coreGraph n L G).sum_degrees_eq_twice_card_edges
  have hd : (∑ p : CoreVertex n L, (coreGraph n L G).degree p)=
      ∑ p∈core n L, coreDegree n L G p := by
    calc
      _=∑ p : CoreVertex n L, coreDegree n L G p.val := by
        apply sum_congr rfl
        intro p hp
        exact certificate_graph_degree n L hL tri ht p
      _=∑ p∈core n L, coreDegree n L G p := sum_attach (core n L) (coreDegree n L G)
  rw [hd] at hs
  have hi := UpperOpenMathCoreDoubleCount.two_core_incidence_sum n L hL tri ht
  change (∑ p∈core n L, coreDegree n L G p)=2*(twoCoreEdges n L G).card at hi
  rw [hi] at hs
  omega

theorem certificate_component_degree {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L)
    (tri : α → Triple) (ht : ∀ a, TrianglePredicate n L (tri a))
    (s : (coreGraph n L (fun a => ofPredicate n L (tri a) hL (ht a))).ConnectedComponent)
    (p : s) : (by
      classical
      exact s.toSimpleGraph.degree p=
        coreDegree n L (fun a => ofPredicate n L (tri a) hL (ht a)) p.val.val) := by
  classical
  let G := fun a => ofPredicate n L (tri a) hL (ht a)
  have hsub : (coreGraph n L G).neighborSet p.val⊆s.supp := by
    intro q hq
    exact s.mem_supp_of_adj_mem_supp p.property hq
  have hd := SimpleGraph.degree_induce_of_neighborSet_subset hsub
  change s.toSimpleGraph.degree p=(coreGraph n L G).degree p.val at hd
  exact hd.trans (certificate_graph_degree n L hL tri ht p.val)

theorem certificate_component_vertex_card {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (G : α → TriangleGeometry)
    (s : (coreGraph n L G).ConnectedComponent) : (by
      classical
      exact Fintype.card s=(componentVertices n L G s).card) := by
  classical
  have heq : (univ : Finset s).image (fun p => p.val.val)=componentVertices n L G s := by
    ext p
    constructor
    · intro hp
      obtain ⟨q,hq,rfl⟩ := mem_image.mp hp
      exact (mem_component n L G s q.val).mpr q.property
    · intro hp
      let pp : CoreVertex n L := ⟨p,component_subset n L G s hp⟩
      have hc := (mem_component n L G s pp).mp hp
      exact mem_image.mpr ⟨⟨pp,hc⟩,mem_univ _,rfl⟩
  have hinj : Function.Injective (fun p : s => p.val.val) := by
    intro p q h
    exact Subtype.ext (Subtype.ext h)
  rw [← heq,card_image_of_injective _ hinj,card_univ]

theorem certificate_component_edge_card {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L)
    (tri : α → Triple) (ht : ∀ a, TrianglePredicate n L (tri a))
    (s : (coreGraph n L (fun a => ofPredicate n L (tri a) hL (ht a))).ConnectedComponent) :
    Nat.card s.toSimpleGraph.edgeSet=
      (componentEdges n L (fun a => ofPredicate n L (tri a) hL (ht a))
        (componentVertices n L (fun a => ofPredicate n L (tri a) hL (ht a)) s)).card := by
  classical
  let G := fun a => ofPredicate n L (tri a) hL (ht a)
  let P := componentVertices n L G s
  rw [Nat.card_eq_fintype_card,← SimpleGraph.edgeFinset_card]
  change s.toSimpleGraph.edgeFinset.card=(componentEdges n L G P).card
  have hs := s.toSimpleGraph.sum_degrees_eq_twice_card_edges
  have hd : (∑ p : s, s.toSimpleGraph.degree p)=∑ p∈P, coreDegree n L G p := by
    calc
      _=∑ p : s, coreDegree n L G p.val.val := by
        apply sum_congr rfl
        intro p hp
        exact certificate_component_degree n L hL tri ht s p
      _=∑ p∈P, coreDegree n L G p := by
        have heq : (univ : Finset s).image (fun p => p.val.val)=P := by
          ext p
          constructor
          · intro hp
            obtain ⟨q,hq,rfl⟩ := mem_image.mp hp
            exact (mem_component n L G s q.val).mpr q.property
          · intro hp
            let pp : CoreVertex n L := ⟨p,component_subset n L G s hp⟩
            have hc := (mem_component n L G s pp).mp hp
            exact mem_image.mpr ⟨⟨pp,hc⟩,mem_univ _,rfl⟩
        have hinj : Set.InjOn (fun p : s => p.val.val) (↑(univ : Finset s) : Set s) := by
          intro p hp q hq h
          exact Subtype.ext (Subtype.ext h)
        rw [← heq,sum_image hinj]
  rw [hd,closed_degree_sum n L G P (component_closed n L hL tri ht s)] at hs
  omega

#print axioms certificate_graph_degree
#print axioms certificate_graph_edge_card
#print axioms certificate_component_degree
#print axioms certificate_component_vertex_card
#print axioms certificate_component_edge_card
end Kobon.UpperOpenMathCoreGraphCounts
