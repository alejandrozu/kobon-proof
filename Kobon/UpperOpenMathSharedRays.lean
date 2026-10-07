import Kobon.UpperOpenMathSectorIncidence

/-!
# Actual shared sides are exactly the two occupied adjacent sectors

Both directions are derived from original certificate-side occurrence fibers.
Positive apex alignment and canonical ray ordering identify the occupied
sector; disjoint interiors exclude putting both incident triangles in the
same sector. No shared-ray equivalence is supplied as a hypothesis.
-/
namespace Kobon.UpperOpenMathSharedRays
open Cells FanGeometry UpperVertexBudget UpperTriangleIncidence UpperSharedIncidence
  UpperOpenMathRadialOrder UpperOpenMathAlignedTriangles UpperOpenMathSectorRecords
  UpperOpenMathSectorIncidence Finset

section Certificate
variable {α : Type*} [Fintype α]
  (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
  (tri : α → Triple) (hi : Function.Injective tri)
  (ht : ∀ a, TrianglePredicate n L (tri a))
  (c : Point) (hc : c∈vertices n L)
  (D : OrderedDirections n L (supports n L c))
  [NeZero (2*(supports n L c).card)] (hcard : 2≤(supports n L c).card)

private noncomputable def geometry : α → TriangleGeometry :=
  fun a => ofPredicate n L (tri a) hL (ht a)

private noncomputable def points : ZMod (2*(supports n L c).card) → Point :=
  D.rayPoint hL hn c hc (fun i hi => (mem_filter.mp hi).2)

include hi in
private theorem disjoint_geometry : Pairwise
    (fun a b => Disjoint (geometry n L hL tri ht a).interior (geometry n L hL tri ht b).interior) := by
  intro a b hab
  exact distinct_interiors_disjoint n L _ _ hL (ht a) (ht b) (fun he => hab (hi he))

include hcard in
private theorem points_injective : Function.Injective (points n L hL hn c hc D) :=
  D.rayPoint_injective hL hn hcard c hc (fun i hi => (mem_filter.mp hi).2)

private theorem points_ne_center (z : ZMod (2*(supports n L c).card)) :
    points n L hL hn c hc D z≠c :=
  D.cyclicPoint_ne_center c z _ (D.rayScale_positive hL hn c hc (fun i hi => (mem_filter.mp hi).2) z)

include hcard in
private theorem side_sector_dichotomy (a : α) (i : Fin 3)
    (z : ZMod (2*(supports n L c).card))
    (he : edge (geometry n L hL tri ht a) i={c,points n L hL hn c hc D z}) :
    (∃ o : Occurrence (geometry n L hL tri ht) c (points n L hL hn c hc D) z, o.index=a) ∨
    (∃ o : Occurrence (geometry n L hL tri ht) c (points n L hL hn c hc D) (z-1), o.index=a) := by
  classical
  let P := points n L hL hn c hc D
  let G := geometry n L hL tri ht
  have hcv : c∈triangleVertices (G a) := by
    apply edge_subset_vertices (G a) i
    simp only [G,he,mem_insert,true_or]
  have hzv : P z∈triangleVertices (G a) := by
    apply edge_subset_vertices (G a) i
    simp [G,he,P]
  obtain ⟨s,hsp,positive,transport⟩ := positive_at_vertex (G a) c hcv
  obtain ⟨w,hq,hr⟩ := aligned_triangle_consecutive n L hL hn tri ht c hc D hcard
    a s transport hsp positive
  rw [← transport.vertices] at hzv
  simp only [triangleVertices,hsp,mem_insert,mem_singleton] at hzv
  have hne := points_ne_center n L hL hn c hc D z
  rcases hzv with hbad|hqz|hrz
  · exact False.elim (hne hbad)
  · have hw : z=w := points_injective n L hL hn c hc D hcard (hqz.trans hq)
    left
    refine ⟨⟨a,s,transport,hsp,?_,?_⟩,rfl⟩
    · simpa only [points,hw] using hq
    · simpa only [points,hw] using hr
  · have hw : z=w+1 := points_injective n L hL hn c hc D hcard (hrz.trans hr)
    have hw' : w=z-1 := by rw [hw]; ring
    right
    refine ⟨⟨a,s,transport,hsp,?_,?_⟩,rfl⟩
    · simpa only [points,hw'] using hq
    · simpa only [points,hw'] using hr

include hi hcard in
/-- Complete actual geometric equivalence between a shared radial edge and
the two selected cells occupying its neighboring sectors. -/
theorem certificate_shared_ray_iff (z : ZMod (2*(supports n L c).card)) :
    {c,D.rayPoint hL hn c hc (fun i hi => (mem_filter.mp hi).2) z}∈
      sharedEdges (fun a => ofPredicate n L (tri a) hL (ht a)) ↔
    z∈triangular (fun a => ofPredicate n L (tri a) hL (ht a)) c
        (D.rayPoint hL hn c hc (fun i hi => (mem_filter.mp hi).2)) ∧
      z-1∈triangular (fun a => ofPredicate n L (tri a) hL (ht a)) c
        (D.rayPoint hL hn c hc (fun i hi => (mem_filter.mp hi).2)) := by
  classical
  let G := geometry n L hL tri ht
  let P := points n L hL hn c hc D
  have hd := disjoint_geometry n L hL tri hi ht
  have pinj := points_injective n L hL hn c hc D hcard
  have pne := points_ne_center n L hL hn c hc D
  change {c,P z}∈sharedEdges G ↔ z∈triangular G c P ∧ z-1∈triangular G c P
  constructor
  · intro he
    have htwo : 1<(univ.filter (fun a : α × Fin 3 => sideMap G a={c,P z})).card := by
      change 1<degree G {c,P z}
      rw [(mem_filter.mp he).2]
      norm_num
    obtain ⟨a,ha,b,hb,hab⟩ := one_lt_card.mp htwo
    have hae := (mem_filter.mp ha).2
    have hbe := (mem_filter.mp hb).2
    have hab' : a.1≠b.1 := by
      intro hh
      have hij : a.2=b.2 := by
        apply edge_injective (G b.1)
        simpa only [sideMap,hh] using hae.trans hbe.symm
      exact hab (Prod.ext hh hij)
    have oa := side_sector_dichotomy n L hL hn tri ht c hc D hcard a.1 a.2 z hae
    have ob := side_sector_dichotomy n L hL hn tri ht c hc D hcard b.1 b.2 z hbe
    rcases oa with ⟨o,ho⟩|⟨o,ho⟩ <;> rcases ob with ⟨p,hp⟩|⟨p,hp⟩
    · exact False.elim (hab' (ho.symm.trans ((occurrence_unique_index G hd o p).trans hp)))
    · exact ⟨(mem_triangular G c P z).mpr ⟨o⟩,(mem_triangular G c P (z-1)).mpr ⟨p⟩⟩
    · exact ⟨(mem_triangular G c P z).mpr ⟨p⟩,(mem_triangular G c P (z-1)).mpr ⟨o⟩⟩
    · exact False.elim (hab' (ho.symm.trans ((occurrence_unique_index G hd o p).trans hp)))
  · rintro ⟨hz,hprev⟩
    obtain ⟨o⟩ := (mem_triangular G c P (z-1)).mp hprev
    obtain ⟨p⟩ := (mem_triangular G c P z).mp hz
    exact shared_of_adjacent_occurrences G hd hcard c P pinj pne z o p

end Certificate

#print axioms certificate_shared_ray_iff
end Kobon.UpperOpenMathSharedRays
