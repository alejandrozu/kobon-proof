import Kobon.UpperOpenMathOrdinaryBaseCover
import Kobon.UpperCleanCharging
import Kobon.UpperOpenMathCoreCapacity

/-!
# Ordinary transverse charges and the extra core-ended-base outcome

Core lines have an additional charge outcome absent from the clean-line
proof. It is recorded separately, so a shared ordinary-to-core side is not
silently assumed to pay only once in a global line count.
-/
namespace Kobon.UpperOpenMathOrdinaryLineCharge
open Cells FanGeometry UpperVertexBudget UpperTriangleIncidence UpperSharedIncidence
  UpperEdgeInventory UpperCoreExtraction UpperCleanCover UpperOpenMathOrdinaryCutParity
  UpperOpenMathOrdinaryBaseCover UpperCleanCharging UpperOpenMathCoreCapacity Finset

def TransverseCharge {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (G : α → TriangleGeometry) (line : Fin n) : Prop :=
  ∃ e : Edge, (e∈edges n L\usedEdges G ∨ e∈oneCoreEdges n L G) ∧
    ∃ p∈e, p∈ordinaryOnLine n L line ∧ ∃ r : Fin n, r≠line ∧ e∈lineEdges n L r

def CoreBaseCharge {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (G : α → TriangleGeometry) (line : Fin n) : Prop :=
  ∃ e∈lineEdges n L line, ∃ q∈e, q∈core n L ∧
    (e∈oneCoreEdges n L G ∨ e∈edges n L\sharedEdges G)

theorem certificate_selected_line_charge {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n) (line : Fin n)
    (heven : n%2=0) (triples : ∀ p∈core n L, (supports n L p).card=3)
    (cut : Line ℝ) (hcut : ∀ p, affineEval cut p=0 ↔ affineEval (L line) p=0)
    (hvalid : cut.a≠0 ∨ cut.b≠0)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a))
    (radial : Point → Fin n) (tip : Point → Point)
    (hrad : ∀ p∈ordinaryOnLine n L line, radial p≠line)
    (hprad : ∀ p∈ordinaryOnLine n L line, affineEval (L (radial p)) p=0)
    (hsel : ∀ p∈ordinaryOnLine n L line, {p,tip p}∈lineEdges n L (radial p))
    (hpos : ∀ p∈ordinaryOnLine n L line, 0<affineEval cut (tip p)) :
    let G := fun a => ofPredicate n L (tri a) hL (ht a)
    TransverseCharge n L G line ∨ CoreBaseCharge n L G line := by
  classical
  let G := fun a => ofPredicate n L (tri a) hL (ht a)
  have indexed : ∀ a, Indexed n L (G a) := fun a => predicate_indexed n L (tri a) hL (ht a)
  have sideInventory : ∀ a i, edge (G a) i∈edges n L :=
    fun a i => predicate_side_mem_edges n L hL hn (tri a) (ht a) i
  have disjoint : Pairwise (fun a b => Disjoint (G a).interior (G b).interior) := by
    intro a b hab
    exact distinct_interiors_disjoint n L _ _ hL (ht a) (ht b) (fun he => hab (hi he))
  rcases selected_degree_or_core_base n L hL hn line heven triples cut hcut hvalid G indexed
    sideInventory radial tip hrad hprad hsel hpos with bad|base
  · left
    obtain ⟨p,hp,hbad⟩ := bad
    let e : Edge := {p,tip p}
    have einv : e∈edges n L := mem_biUnion.mpr ⟨radial p,mem_univ _,hsel p hp⟩
    refine ⟨e,?_,p,by simp [e],hp,radial p,hrad p hp,hsel p hp⟩
    by_cases used : e∈usedEdges G
    · right
      have dpos := degree_pos G used
      have dmax := degree_le_two G disjoint e
      have dtwo : degree G e=2 := by change degree G e≠1 at hbad; omega
      exact mem_filter.mpr ⟨mem_filter.mpr ⟨used,dtwo⟩,p,by simp [e],(mem_filter.mp hp).2⟩
    · exact Or.inl (mem_sdiff.mpr ⟨einv,used⟩)
  · right
    obtain ⟨e,he,q,hqe,hqc⟩ := base
    have heBase := (mem_filter.mp he).1
    have touch := (mem_filter.mp he).2
    obtain ⟨⟨a,i⟩,hai,heq⟩ := mem_image.mp heBase
    have einv : e∈edges n L := by simpa only [← heq,sideMap] using sideInventory a i
    have hon := (mem_filter.mp hai).2.1
    have lineEdge := inventory_on_support n L hL hn line e einv
      (fun p hp => (hcut p).mp (hon p (by simpa only [heq] using hp)))
    refine ⟨e,lineEdge,q,hqe,hqc,?_⟩
    by_cases shared : e∈sharedEdges G
    · exact Or.inl (mem_filter.mpr ⟨shared,touch⟩)
    · exact Or.inr (mem_sdiff.mpr ⟨einv,shared⟩)

theorem certificate_all_line_charge {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 4≤n)
    (heven : n%2=0) (triples : ∀ p∈core n L, (supports n L p).card=3)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a)) (line : Fin n) :
    let G := fun a => ofPredicate n L (tri a) hL (ht a)
    TransverseCharge n L G line ∨ CoreBaseCharge n L G line := by
  have nc := not_concurrent_of_triples n L hL hn triples
  obtain ⟨cut,valid,cut_eq,side⟩ := common_positive_cut_ordinary n L hL (by omega) nc line
  obtain ⟨radial,tip,hrad,hprad,hsel,hpos⟩ := ordinary_endpoint_selectors n L hL line cut side
  exact certificate_selected_line_charge n L hL (by omega) line heven triples cut cut_eq valid
    tri hi ht radial tip hrad hprad hsel hpos

#print axioms certificate_selected_line_charge
#print axioms certificate_all_line_charge
end Kobon.UpperOpenMathOrdinaryLineCharge
