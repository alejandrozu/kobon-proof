import Kobon.UpperTriangleIncidence
import Kobon.UpperSharedIncidence

/-! Transport of actual triangles to a selected apex and positive orientation.
The interior, vertex set, indexed support property, weak-side tests and side
occurrence map are all retained. These facts allow local sector extraction
to keep the original certificate index rather than silently changing cells. -/
namespace Kobon.UpperOpenMathAlignedTriangles
open Cells UpperTriangleIncidence UpperSharedIncidence Finset

noncomputable def reverse (t : TriangleGeometry) : TriangleGeometry where
  p := t.p
  q := t.r
  r := t.q
  A := t.A
  B := t.C
  C := t.B
  nondegenerate := by
    have he : areaDet t.p t.r t.q= -areaDet t.p t.q t.r := by dsimp [areaDet]; ring
    rw [he]
    exact neg_ne_zero.mpr t.nondegenerate
  Aq := t.Ar
  Ar := t.Aq
  Bp := t.Cp
  Br := t.Cq
  Cp := t.Bp
  Cq := t.Br
  Ap := t.Ap
  Bq := t.Cr
  Cr := t.Bq

noncomputable def triangleVertices (t : TriangleGeometry) : Finset Point := by
  classical
  exact {t.p,t.q,t.r}

@[simp] theorem reverse_interior (t : TriangleGeometry) : (reverse t).interior=t.interior := by
  ext x
  constructor
  · rintro ⟨u,v,w,hu,hv,hw,hs,hx⟩
    refine ⟨u,w,v,hu,hw,hv,by linarith,?_⟩
    rw [hx]
    apply Prod.ext <;> dsimp [reverse,barycenter] <;> ring
  · rintro ⟨u,v,w,hu,hv,hw,hs,hx⟩
    refine ⟨u,w,v,hu,hw,hv,by linarith,?_⟩
    rw [hx]
    apply Prod.ext <;> dsimp [reverse,barycenter] <;> ring

@[simp] theorem cycle_vertices (t : TriangleGeometry) :
    triangleVertices (cycle t)=triangleVertices t := by
  classical
  ext x
  simp only [triangleVertices,cycle,mem_insert,mem_singleton]
  tauto

@[simp] theorem reverse_vertices (t : TriangleGeometry) :
    triangleVertices (reverse t)=triangleVertices t := by
  classical
  ext x
  simp only [triangleVertices,reverse,mem_insert,mem_singleton]
  tauto

theorem cycle_side_map (t : TriangleGeometry) (i : Fin 3) :
    ∃ j : Fin 3, edge (cycle t) i=edge t j := by
  classical
  fin_cases i
  · exact ⟨1,by simp [edge,sideTriangle,cycle]⟩
  · exact ⟨2,by simp [edge,sideTriangle,cycle]⟩
  · exact ⟨0,by simp [edge,sideTriangle,cycle]⟩

theorem reverse_side_map (t : TriangleGeometry) (i : Fin 3) :
    ∃ j : Fin 3, edge (reverse t) i=edge t j := by
  classical
  fin_cases i
  · exact ⟨2,by simp [edge,sideTriangle,cycle,reverse,pair_comm]⟩
  · exact ⟨1,by simp [edge,sideTriangle,cycle,reverse,pair_comm]⟩
  · exact ⟨0,by simp [edge,sideTriangle,cycle,reverse,pair_comm]⟩

structure Transport (s t : TriangleGeometry) : Prop where
  interior : s.interior=t.interior
  vertices : triangleVertices s=triangleVertices t
  sides : ∀ i : Fin 3, ∃ j : Fin 3, edge s i=edge t j
  indexed : ∀ n L, Indexed n L t → Indexed n L s
  weak : ∀ l : Line ℝ, WeakSide l t.p t.q t.r → WeakSide l s.p s.q s.r

theorem Transport.refl (t : TriangleGeometry) : Transport t t :=
  ⟨rfl,rfl,fun i => ⟨i,rfl⟩,fun _ _ h => h,fun _ h => h⟩

theorem Transport.trans {s t u : TriangleGeometry}
    (h : Transport s t) (k : Transport t u) : Transport s u := by
  refine ⟨h.interior.trans k.interior,h.vertices.trans k.vertices,?_,?_,?_⟩
  · intro i
    obtain ⟨j,hj⟩ := h.sides i
    obtain ⟨a,ha⟩ := k.sides j
    exact ⟨a,hj.trans ha⟩
  · intro n L hh
    exact h.indexed n L (k.indexed n L hh)
  · intro l hh
    exact h.weak l (k.weak l hh)

theorem cycle_transport (t : TriangleGeometry) : Transport (cycle t) t := by
  refine ⟨cycle_interior t,cycle_vertices t,cycle_side_map t,?_,?_⟩
  · intro n L h
    exact cycle_indexed h
  · intro l h
    rcases h with ⟨hp,hq,hr⟩|⟨hp,hq,hr⟩
    · exact Or.inl ⟨hq,hr,hp⟩
    · exact Or.inr ⟨hq,hr,hp⟩

theorem reverse_transport (t : TriangleGeometry) : Transport (reverse t) t := by
  refine ⟨reverse_interior t,reverse_vertices t,reverse_side_map t,?_,?_⟩
  · intro n L h
    obtain ⟨a,b,c,ha,hb,hc⟩ := h
    exact ⟨a,c,b,ha,hc,hb⟩
  · intro l h
    rcases h with ⟨hp,hq,hr⟩|⟨hp,hq,hr⟩
    · exact Or.inl ⟨hp,hr,hq⟩
    · exact Or.inr ⟨hp,hr,hq⟩

theorem positive_orientation (t : TriangleGeometry) :
    ∃ s : TriangleGeometry, s.p=t.p ∧ 0<areaDet s.p s.q s.r ∧ Transport s t := by
  rcases lt_or_gt_of_ne t.nondegenerate with hn|hp
  · refine ⟨reverse t,rfl,?_,reverse_transport t⟩
    have he : areaDet (reverse t).p (reverse t).q (reverse t).r= -areaDet t.p t.q t.r := by
      dsimp [reverse,areaDet]
      ring
    rw [he]
    linarith
  · exact ⟨t,rfl,hp,Transport.refl t⟩

/-- Every actual triangle at the chosen vertex admits a positive apex
alignment preserving its original cell and original side occurrences. -/
theorem positive_at_vertex (t : TriangleGeometry) (c : Point)
    (hc : c∈triangleVertices t) :
    ∃ s : TriangleGeometry, s.p=c ∧ 0<areaDet s.p s.q s.r ∧ Transport s t := by
  classical
  simp only [triangleVertices,mem_insert,mem_singleton] at hc
  rcases hc with hc|hc|hc
  · obtain ⟨s,hsp,hs,htr⟩ := positive_orientation t
    exact ⟨s,hsp.trans hc.symm,hs,htr⟩
  · obtain ⟨s,hsp,hs,htr⟩ := positive_orientation (cycle t)
    exact ⟨s,hsp.trans hc.symm,hs,htr.trans (cycle_transport t)⟩
  · obtain ⟨s,hsp,hs,htr⟩ := positive_orientation (cycle (cycle t))
    exact ⟨s,hsp.trans hc.symm,hs,
      htr.trans ((cycle_transport (cycle t)).trans (cycle_transport t))⟩

#print axioms positive_at_vertex
#print axioms Transport.trans
end Kobon.UpperOpenMathAlignedTriangles
