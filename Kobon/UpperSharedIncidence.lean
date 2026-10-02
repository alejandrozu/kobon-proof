import Kobon.UpperTriangleIncidence
import Kobon.UpperSharedEdge

/-!
# Shared-side extraction and the finite core-edge budget

The supports of every triangle are actual indexed arrangement lines. Shared
sides are extracted from the finite side-occurrence fibers. Their multiple
endpoints follow from geometry, and the shared sides are partitioned into
ordinary-to-core and core-to-core classes. Total elementary-edge enumeration
and clean-line charging are separate remaining obligations.
-/
namespace Kobon.UpperSharedIncidence
open Cells FanGeometry UpperTriangleIncidence Finset

def Indexed (n : ℕ) (L : ℕ → Line ℝ) (t : TriangleGeometry) : Prop :=
  ∃ a b c : Fin n, t.A=L a ∧ t.B=L b ∧ t.C=L c

theorem cycle_indexed {n : ℕ} {L : ℕ → Line ℝ} {t : TriangleGeometry}
    (h : Indexed n L t) : Indexed n L (cycle t) := by
  obtain ⟨a,b,c,ha,hb,hc⟩ := h
  exact ⟨b,c,a,hb,hc,ha⟩

theorem swap_indexed {n : ℕ} {L : ℕ → Line ℝ} {t : TriangleGeometry}
    (h : Indexed n L t) : Indexed n L (swap t) := by
  obtain ⟨a,b,c,ha,hb,hc⟩ := h
  exact ⟨b,a,c,hb,ha,hc⟩

theorem sideTriangle_indexed {n : ℕ} {L : ℕ → Line ℝ} {t : TriangleGeometry}
    (h : Indexed n L t) (i : Fin 3) : Indexed n L (sideTriangle t i) := by
  fin_cases i <;> simp only [sideTriangle,Fin.reduceFinMk,ite_true,ite_false]
  · exact h
  · exact cycle_indexed h
  · exact cycle_indexed (cycle_indexed h)

theorem predicate_indexed (n : ℕ) (L : ℕ → Line ℝ) (tri : Triple)
    (hL : NoParallel n L) (ht : TrianglePredicate n L tri) :
    Indexed n L (ofPredicate n L tri hL ht) := by
  have hi : tri.i<n := by have := ht.1; have := ht.2.1; have := ht.2.2.1; omega
  have hj : tri.j<n := by have := ht.2.1; have := ht.2.2.1; omega
  exact ⟨⟨tri.k,ht.2.2.1⟩,⟨tri.j,hj⟩,⟨tri.i,hi⟩,rfl,rfl,rfl⟩

theorem align_edge_indexed {n : ℕ} {L : ℕ → Line ℝ}
    (t : TriangleGeometry) (ht : Indexed n L t) (i : Fin 3)
    (p q : Point) (he : edge t i={p,q}) :
    ∃ s : TriangleGeometry, s.p=p ∧ s.q=q ∧ s.interior=t.interior ∧ Indexed n L s := by
  classical
  let s := sideTriangle t i
  have hs : Indexed n L s := sideTriangle_indexed ht i
  have hsp : s.p=p ∨ s.p=q := by
    have h : s.p∈edge t i := by simp [edge,s]
    simpa only [he,mem_insert,mem_singleton] using h
  have hsq : s.q=p ∨ s.q=q := by
    have h : s.q∈edge t i := by simp [edge,s]
    simpa only [he,mem_insert,mem_singleton] using h
  have hne := nondegenerate_pair_ne s.p s.q s.r s.nondegenerate
  rcases hsp with hsp|hsp <;> rcases hsq with hsq|hsq
  · exact False.elim (hne (hsp.trans hsq.symm))
  · exact ⟨s,hsp,hsq,sideTriangle_interior t i,hs⟩
  · exact ⟨swap s,hsq,hsp,by simp [s],swap_indexed hs⟩
  · exact False.elim (hne (hsp.trans hsq.symm))

/-- Aligning the geometric triangles along a shared side also identifies
their supporting arrangement-line indices, using nonparallelness. -/
theorem nonordinary_of_aligned_pair {n : ℕ} {L : ℕ → Line ℝ}
    (hL : NoParallel n L) (s t : TriangleGeometry)
    (hs : Indexed n L s) (ht : Indexed n L t)
    (hp : t.p=s.p) (hq : t.q=s.q)
    (hd : Disjoint s.interior t.interior) :
    ¬OrdinaryAt n L s.p ∨ ¬OrdinaryAt n L s.q := by
  obtain ⟨a,b,c,ha,hb,hc⟩ := hs
  obtain ⟨d,e,f,hd',he,hf⟩ := ht
  have hcf : c=f := by
    by_contra hh
    have hpq := nondegenerate_pair_ne s.p s.q s.r s.nondegenerate
    apply hpq
    apply two_lines_two_points (L c) (L f) s.p s.q
      (noParallel_any n L hL c f c.isLt f.isLt (fun h => hh (Fin.ext h)))
    · simpa only [hc] using s.Cp
    · simpa only [hc] using s.Cq
    · simpa only [hf,hp] using t.Cp
    · simpa only [hf,hq] using t.Cq
  let pair : UpperSharedEdge.Pair n L :=
    ⟨s,t,c,a,b,d,e,hp,hq,hc,by simpa only [hcf] using hf,ha,hb,hd',he⟩
  exact pair.has_nonordinary_endpoint hL hd

section Finite
variable {α : Type*} [Fintype α] (n : ℕ) (L : ℕ → Line ℝ)
  (t : α → TriangleGeometry)

/-- Shared sides are derived from actual side-occurrence fibers, and each
has a nonordinary endpoint. This is not an assumed edge classification. -/
theorem shared_has_nonordinary_endpoint (hL : NoParallel n L)
    (ht : ∀ a, Indexed n L (t a))
    (hd : Pairwise (fun a b => Disjoint (t a).interior (t b).interior))
    {e : Edge} (he : e∈sharedEdges t) :
    ∃ p∈e, ¬OrdinaryAt n L p := by
  classical
  obtain ⟨heused,hedeg⟩ := mem_filter.mp he
  obtain ⟨p,q,hpq,hepq⟩ := card_eq_two.mp (used_edge_card t heused)
  have htwo : 1<(univ.filter (fun a : α × Fin 3 => sideMap t a=e)).card := by
    change 1<degree t e
    omega
  obtain ⟨a,ha,b,hb,hab⟩ := one_lt_card.mp htwo
  have hae := (mem_filter.mp ha).2
  have hbe := (mem_filter.mp hb).2
  have hab' : a.1≠b.1 := by
    intro hh
    have hij : a.2=b.2 := by
      apply edge_injective (t b.1)
      simpa only [sideMap,hh] using hae.trans hbe.symm
    exact hab (Prod.ext hh hij)
  obtain ⟨s,hsp,hsq,hsi,hs⟩ := align_edge_indexed (t a.1) (ht a.1) a.2 p q (hae.trans hepq)
  obtain ⟨u,hup,huq,hui,hu⟩ := align_edge_indexed (t b.1) (ht b.1) b.2 p q (hbe.trans hepq)
  have hdu : Disjoint s.interior u.interior := by rw [hsi,hui]; exact hd hab'
  have hc := nonordinary_of_aligned_pair hL s u hs hu
    (hup.trans hsp.symm) (huq.trans hsq.symm) hdu
  simp only [hsp,hsq] at hc
  rcases hc with hc|hc
  · exact ⟨p,by simp [hepq],hc⟩
  · exact ⟨q,by simp [hepq],hc⟩

noncomputable def oneCoreEdges : Finset Edge := by
  classical
  exact (sharedEdges t).filter (fun e => ∃ p∈e, OrdinaryAt n L p)

noncomputable def twoCoreEdges : Finset Edge := by
  classical
  exact sharedEdges t\oneCoreEdges n L t

theorem shared_partition :
    (oneCoreEdges n L t).card+(twoCoreEdges n L t).card=(sharedEdges t).card := by
  classical
  have hs : oneCoreEdges n L t⊆sharedEdges t := filter_subset _ _
  have hh := card_sdiff_add_card_eq_card hs
  dsimp [twoCoreEdges]
  omega

theorem twoCore_endpoints {e : Edge} (he : e∈twoCoreEdges n L t) :
    ∀ p∈e, ¬OrdinaryAt n L p := by
  classical
  obtain ⟨hs,hn⟩ := mem_sdiff.mp he
  intro p hp ho
  exact hn (mem_filter.mpr ⟨hs,⟨p,hp,ho⟩⟩)

theorem oneCore_has_both_kinds (hL : NoParallel n L)
    (ht : ∀ a, Indexed n L (t a))
    (hd : Pairwise (fun a b => Disjoint (t a).interior (t b).interior))
    {e : Edge} (he : e∈oneCoreEdges n L t) :
    (∃ p∈e, OrdinaryAt n L p) ∧ (∃ p∈e, ¬OrdinaryAt n L p) := by
  classical
  obtain ⟨hs,ho⟩ := mem_filter.mp he
  exact ⟨ho,shared_has_nonordinary_endpoint n L t hL ht hd hs⟩

/-- The finite side-incidence identity with the two geometrically justified
shared-edge classes. The finite edge universe is explicit. -/
theorem core_incidence
    (hd : Pairwise (fun a b => Disjoint (t a).interior (t b).interior))
    (E : Finset Edge) (hE : usedEdges t⊆E) :
    3*Fintype.card α+(E\usedEdges t).card=
      E.card+(oneCoreEdges n L t).card+(twoCoreEdges n L t).card := by
  have hi := exact_incidence_with_unused t hd E hE
  have hs := shared_partition n L t
  omega

end Finite

#print axioms shared_has_nonordinary_endpoint
#print axioms oneCore_has_both_kinds
#print axioms core_incidence
end Kobon.UpperSharedIncidence
