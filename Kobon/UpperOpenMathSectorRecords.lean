import Kobon.UpperOpenMathRayEndpoints
import Kobon.UpperOpenMathAlignedTriangles
import Kobon.UpperFan
import Kobon.UpperOpenMathCyclicAdjacency
import Kobon.UpperOpenMathSectorCut

/-!
# Actual certificate identities retained in local sector records

Every positive reorientation of an actual selected triangle retains its
original certificate index. Its two radial sides map to the unique actual
first endpoints of the canonical rays. Sector records keep this association
when constructing a `Sectors` record, so later shared-edge matching need not
guess which two triangles occupied a radial side.
-/
namespace Kobon.UpperOpenMathSectorRecords
open Cells FanGeometry UpperVertexBudget UpperEdgeInventory UpperTriangleIncidence
  UpperSharedIncidence UpperOpenMathRadialOrder UpperOpenMathAlignedTriangles Finset

theorem transported_side_used {α : Type*} [Fintype α]
    (geometry : α → TriangleGeometry) (a : α) (s : TriangleGeometry)
    (hs : Transport s (geometry a)) (i : Fin 3) : edge s i∈usedEdges geometry := by
  classical
  obtain ⟨j,hj⟩ := hs.sides i
  exact mem_image.mpr ⟨(a,j),mem_univ _,hj.symm⟩

theorem used_edge_has_ray {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (ht : ∀ a, TrianglePredicate n L (tri a))
    (c : Point) (hc : c∈vertices n L)
    (D : OrderedDirections n L (supports n L c))
    [NeZero (2*(supports n L c).card)] (q : Point) (hqc : q≠c)
    (he : {c,q}∈usedEdges (fun a => ofPredicate n L (tri a) hL (ht a))) :
    ∃ z : ZMod (2*(supports n L c).card),
      D.rayPoint hL hn c hc (fun i hi => (mem_filter.mp hi).2) z=q := by
  classical
  have hinv := certificate_sides_subset n L hL hn tri ht he
  obtain ⟨i,_,hei⟩ := mem_biUnion.mp hinv
  have hci := edge_endpoints_on_line n L hL hn hei c (by simp)
  have hqi := edge_endpoints_on_line n L hL hn hei q (by simp)
  have hqv := certificate_side_vertices n L hL tri ht he (by simp : q∈({c,q} : Edge))
  obtain ⟨z,_,hz⟩ := D.incident_edge_has_ray hL hn c hc
    (fun j hj => (mem_filter.mp hj).2) i (mem_filter.mpr ⟨mem_univ i,hci⟩)
    q (mem_filter.mpr ⟨hqv,hqi⟩) hqc hei
  exact ⟨z,hz⟩

/-- The side-to-ray association is derived from actual selected triangle
sides and the actual elementary inventory; it is not a premise. -/
theorem aligned_triangle_has_rays {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (ht : ∀ a, TrianglePredicate n L (tri a))
    (c : Point) (hc : c∈vertices n L)
    (D : OrderedDirections n L (supports n L c))
    [NeZero (2*(supports n L c).card)]
    (a : α) (s : TriangleGeometry)
    (hs : Transport s (ofPredicate n L (tri a) hL (ht a))) (hp : s.p=c) :
    ∃ z w : ZMod (2*(supports n L c).card),
      s.q=D.rayPoint hL hn c hc (fun i hi => (mem_filter.mp hi).2) z ∧
      s.r=D.rayPoint hL hn c hc (fun i hi => (mem_filter.mp hi).2) w := by
  let geometry := fun a => ofPredicate n L (tri a) hL (ht a)
  have hq : s.q≠c := by
    rw [← hp]
    exact (nondegenerate_pair_ne s.p s.q s.r s.nondegenerate).symm
  have hr : s.r≠c := by
    intro he
    apply s.Ap
    simpa only [he,← hp] using s.Ar
  have hEq : {c,s.q}∈usedEdges geometry := by
    have he := transported_side_used geometry a s hs 0
    simpa only [edge,sideTriangle,Fin.reduceFinMk,ite_true,hp] using he
  have hEr : {c,s.r}∈usedEdges geometry := by
    have he := transported_side_used geometry a s hs 2
    simpa [edge,sideTriangle,cycle,hp,pair_comm] using he
  obtain ⟨z,hz⟩ := used_edge_has_ray n L hL hn tri ht c hc D s.q hq hEq
  obtain ⟨w,hw⟩ := used_edge_has_ray n L hL hn tri ht c hc D s.r hr hEr
  exact ⟨z,w,hz.symm,hw.symm⟩

structure Occurrence {α : Type*} (geometry : α → TriangleGeometry)
    {r : ℕ} [NeZero (2*r)] (c : Point) (P : ZMod (2*r) → Point)
    (z : ZMod (2*r)) where
  index : α
  triangle : TriangleGeometry
  transport : Transport triangle (geometry index)
  center : triangle.p=c
  left : triangle.q=P z
  right : triangle.r=P (z+1)

/-- A positive alignment of any actual selected triangle at the core has
two consecutive canonical ray endpoints. The adjacency assertion is derived
from the triangle's weak-side tests and the ordered direction geometry. -/
theorem aligned_triangle_consecutive {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (ht : ∀ a, TrianglePredicate n L (tri a))
    (c : Point) (hc : c∈vertices n L)
    (D : OrderedDirections n L (supports n L c))
    [NeZero (2*(supports n L c).card)] (hcard : 2≤(supports n L c).card)
    (a : α) (s : TriangleGeometry)
    (hs : Transport s (ofPredicate n L (tri a) hL (ht a)))
    (hp : s.p=c) (positive : 0<areaDet s.p s.q s.r) :
    ∃ z : ZMod (2*(supports n L c).card),
      s.q=D.rayPoint hL hn c hc (fun i hi => (mem_filter.mp hi).2) z ∧
      s.r=D.rayPoint hL hn c hc (fun i hi => (mem_filter.mp hi).2) (z+1) := by
  let P := D.rayPoint hL hn c hc (fun i hi => (mem_filter.mp hi).2)
  obtain ⟨z,w,hq,hr⟩ := aligned_triangle_has_rays n L hL hn tri ht c hc D a s hs hp
  have hscale := D.rayScale_positive hL hn c hc (fun i hi => (mem_filter.mp hi).2)
  have hpos : 0<areaDet c (P z) (P w) := by simpa only [hp,hq,hr] using positive
  have hvec : 0<UpperOpenMathCyclicAdjacency.cross (D.cyclicVector z) (D.cyclicVector w) := by
    exact (D.cyclicPoint_area_positive_iff c z w _ _ (hscale z) (hscale w)).mp hpos
  have hw : w=z+1 := by
    by_contra hne
    have hv := UpperOpenMathCyclicAdjacency.next_inside_positive_wedge D hcard z w hvec hne
    have hleft : 0<areaDet c (P z) (P (z+1)) :=
      D.rayPoint_positive_orientation hL hn hcard c hc (fun i hi => (mem_filter.mp hi).2) z
    have hright : 0<areaDet c (P (z+1)) (P w) :=
      (D.cyclicPoint_area_positive_iff c (z+1) w _ _ (hscale (z+1)) (hscale w)).mpr hv
    let i := D.cyclicRadial (z+1)
    apply UpperOpenMathSectorCut.no_intermediate_ray s (L i) (P (z+1))
      (line_valid n L hL hn i)
    · rw [hp]
      exact (mem_filter.mp (D.cyclicRadial_mem (z+1))).2
    · exact D.rayPoint_on_line hL hn c hc (fun j hj => (mem_filter.mp hj).2) (z+1)
    · exact hs.weak (L i) (weakSide_of_predicate n L (tri a) hL (ht a) i)
    · simpa only [hp,hq] using hleft
    · simpa only [hp,hr] using hright
  refine ⟨z,hq,?_⟩
  simpa only [hw] using hr

theorem aligned_triangle_occurs {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L) (hn : 2≤n)
    (tri : α → Triple) (ht : ∀ a, TrianglePredicate n L (tri a))
    (c : Point) (hc : c∈vertices n L)
    (D : OrderedDirections n L (supports n L c))
    [NeZero (2*(supports n L c).card)] (hcard : 2≤(supports n L c).card)
    (a : α) (s : TriangleGeometry)
    (hs : Transport s (ofPredicate n L (tri a) hL (ht a)))
    (hp : s.p=c) (positive : 0<areaDet s.p s.q s.r) :
    ∃ z : ZMod (2*(supports n L c).card), Nonempty
      (Occurrence (fun a => ofPredicate n L (tri a) hL (ht a)) c
        (D.rayPoint hL hn c hc (fun i hi => (mem_filter.mp hi).2)) z) := by
  obtain ⟨z,hq,hr⟩ := aligned_triangle_consecutive n L hL hn tri ht c hc D hcard a s hs hp positive
  exact ⟨z,⟨⟨a,s,hs,hp,hq,hr⟩⟩⟩

noncomputable def defaultTriangle : TriangleGeometry where
  p := (0,0)
  q := (1,0)
  r := (0,1)
  A := ⟨1,1,1⟩
  B := ⟨1,0,0⟩
  C := ⟨0,1,0⟩
  nondegenerate := by norm_num [areaDet]
  Aq := by norm_num [affineEval]
  Ar := by norm_num [affineEval]
  Bp := by norm_num [affineEval]
  Br := by norm_num [affineEval]
  Cp := by norm_num [affineEval]
  Cq := by norm_num [affineEval]
  Ap := by norm_num [affineEval]
  Bq := by norm_num [affineEval]
  Cr := by norm_num [affineEval]

section FanRecord
variable {α : Type*} {n r : ℕ} [NeZero (2*r)] {L : ℕ → Line ℝ}
  (geometry : α → TriangleGeometry) (indexed : ∀ a, Indexed n L (geometry a))
  (c : Point) (P : ZMod (2*r) → Point)

noncomputable def triangular : Finset (ZMod (2*r)) := by
  classical
  exact univ.filter (fun z => Nonempty (Occurrence geometry c P z))

theorem mem_triangular (z : ZMod (2*r)) :
    z∈triangular geometry c P ↔ Nonempty (Occurrence geometry c P z) := by
  classical
  simp [triangular]

noncomputable def chosenOccurrence (z : ZMod (2*r))
    (hz : z∈triangular geometry c P) : Occurrence geometry c P z :=
  Classical.choice ((mem_triangular geometry c P z).mp hz)

noncomputable def sectorTriangle (z : ZMod (2*r)) : TriangleGeometry := by
  classical
  exact if hz : z∈triangular geometry c P then
    (chosenOccurrence geometry c P z hz).triangle else defaultTriangle

noncomputable def opposite (hn : 1≤n) (z : ZMod (2*r)) : Fin n := by
  classical
  by_cases hz : z∈triangular geometry c P
  · let o := chosenOccurrence geometry c P z hz
    have hi := o.transport.indexed n L (indexed o.index)
    exact Classical.choose hi
  · exact ⟨0,by omega⟩

theorem opposite_spec (hn : 1≤n) (z : ZMod (2*r))
    (hz : z∈triangular geometry c P) :
    (sectorTriangle geometry c P z).A=L (opposite geometry indexed c P hn z) := by
  classical
  unfold sectorTriangle opposite
  rw [dif_pos hz,dif_pos hz]
  have hi := Classical.choose_spec
    ((chosenOccurrence geometry c P z hz).transport.indexed n L
      (indexed (chosenOccurrence geometry c P z hz).index))
  obtain ⟨b,d,hA,_,_⟩ := hi
  exact hA

/-- Build an actual geometric fan while retaining original certificate
indices in every triangular sector. Empty sectors use an auxiliary triangle
whose fields are never asserted to be an arrangement cell. -/
noncomputable def sectors (hn : 1≤n) (R : ZMod (2*r) → Fin n)
    (radial_center : ∀ z, affineEval (L (R z)) c=0)
    (radial_point : ∀ z, affineEval (L (R z)) (P z)=0)
    (antipodal : ∀ z, ∃ v : ℝ, 0<v ∧ P (z+(r : ZMod (2*r)))=
      (c.1-v*((P z).1-c.1),c.2-v*((P z).2-c.2))) : UpperFan.Sectors n r L where
  center := c
  point := P
  radial := R
  opposite := opposite geometry indexed c P hn
  triangular := triangular geometry c P
  triangle := sectorTriangle geometry c P
  radial_center := radial_center
  radial_point := radial_point
  antipodal := antipodal
  triangle_center := by
    intro z hz
    simp only [sectorTriangle,dif_pos hz]
    exact (chosenOccurrence geometry c P z hz).center
  triangle_left := by
    intro z hz
    simp only [sectorTriangle,dif_pos hz]
    exact (chosenOccurrence geometry c P z hz).left
  triangle_right := by
    intro z hz
    simp only [sectorTriangle,dif_pos hz]
    exact (chosenOccurrence geometry c P z hz).right
  triangle_support := opposite_spec geometry indexed c P hn

end FanRecord

#print axioms aligned_triangle_has_rays
#print axioms aligned_triangle_occurs
#print axioms sectors
end Kobon.UpperOpenMathSectorRecords
