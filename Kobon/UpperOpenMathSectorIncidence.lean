import Kobon.UpperOpenMathSectorRecords

/-!
# Certificate occurrence uniqueness and shared radial sides

Distinct sectors at one actual apex retain distinct original triangle
identities. Adjacent occupied sectors therefore give two different original
side occurrences of their common radial edge, and actual geometric capacity
two proves that the edge is shared.
-/
namespace Kobon.UpperOpenMathSectorIncidence
open Cells UpperTriangleIncidence UpperOpenMathAlignedTriangles
  UpperOpenMathSectorRecords Finset

theorem cyclic_one_ne_zero (r : ℕ) [NeZero (2*r)] (hr : 2≤r) :
    (1 : ZMod (2*r))≠0 := by
  intro he
  have hv := congrArg ZMod.val he
  have h1 : (1 : ZMod (2*r)).val=1 := by
    simpa only [Nat.cast_one] using (ZMod.val_natCast_of_lt (n:=2*r) (a:=1) (by omega))
  rw [h1,ZMod.val_zero] at hv
  omega

theorem cyclic_two_ne_zero (r : ℕ) [NeZero (2*r)] (hr : 2≤r) :
    (2 : ZMod (2*r))≠0 := by
  intro he
  have hv := congrArg ZMod.val he
  have h2 : (2 : ZMod (2*r)).val=2 := by
    simpa only [Nat.cast_ofNat] using (ZMod.val_natCast_of_lt (n:=2*r) (a:=2) (by omega))
  rw [h2,ZMod.val_zero] at hv
  omega

theorem cyclic_previous_ne (r : ℕ) [NeZero (2*r)] (hr : 2≤r)
    (z : ZMod (2*r)) : z-1≠z := by
  intro he
  have hh : z+1=z := by
    have ha := congrArg (fun x : ZMod (2*r) => x+1) he
    simpa only [sub_add_cancel] using ha.symm
  apply cyclic_one_ne_zero r hr
  apply add_left_cancel (a:=z)
  simpa only [add_zero] using hh

theorem edge_subset_vertices (t : TriangleGeometry) (i : Fin 3) :
    edge t i⊆triangleVertices t := by
  classical
  fin_cases i
  all_goals
    intro x hx
    simp only [edge,sideTriangle,cycle,Fin.reduceFinMk,ite_true,ite_false,
      mem_insert,mem_singleton] at hx
    simp only [triangleVertices,mem_insert,mem_singleton]
    tauto

theorem occurrence_vertices {α : Type*} (geometry : α → TriangleGeometry)
    {r : ℕ} [NeZero (2*r)] {c : Point} {P : ZMod (2*r) → Point}
    {z : ZMod (2*r)} (o : Occurrence geometry c P z) :
    triangleVertices (geometry o.index)={c,P z,P (z+1)} := by
  rw [← o.transport.vertices]
  simp only [triangleVertices,o.center,o.left,o.right]

theorem occurrence_index_injective {α : Type*} (geometry : α → TriangleGeometry)
    {r : ℕ} [NeZero (2*r)] (hr : 2≤r) (c : Point) (P : ZMod (2*r) → Point)
    (pinj : Function.Injective P) (pne : ∀ z, P z≠c)
    {z w : ZMod (2*r)} (o : Occurrence geometry c P z)
    (p : Occurrence geometry c P w) (hi : o.index=p.index) : z=w := by
  classical
  have he : ({c,P z,P (z+1)} : Finset Point)={c,P w,P (w+1)} := by
    rw [← occurrence_vertices geometry o,← occurrence_vertices geometry p,hi]
  have hz : P z=P w ∨ P z=P (w+1) := by
    have hm : P z∈({c,P w,P (w+1)} : Finset Point) := by rw [← he]; simp
    simpa only [mem_insert,mem_singleton,or_iff_right (pne z)] using hm
  rcases hz with hz|hz
  · exact pinj hz
  · have hz' : z=w+1 := pinj hz
    have hn : P (z+1)=P w ∨ P (z+1)=P (w+1) := by
      have hm : P (z+1)∈({c,P w,P (w+1)} : Finset Point) := by rw [← he]; simp
      simpa only [mem_insert,mem_singleton,or_iff_right (pne (z+1))] using hm
    rcases hn with hn|hn
    · have hn' : z+1=w := pinj hn
      have htwo : z+2=z := by
        calc
          z+2=(z+1)+1 := by ring
          _=w+1 := by rw [hn']
          _=z := hz'.symm
      exact False.elim (cyclic_two_ne_zero r hr (add_left_cancel (by simpa only [add_zero] using htwo)))
    · have hn' : z+1=w+1 := pinj hn
      exact add_right_cancel hn'

theorem occurrence_unique_index {α : Type*} (geometry : α → TriangleGeometry)
    (disjoint : Pairwise (fun a b => Disjoint (geometry a).interior (geometry b).interior))
    {r : ℕ} [NeZero (2*r)] {c : Point} {P : ZMod (2*r) → Point}
    {z : ZMod (2*r)} (o p : Occurrence geometry c P z) : o.index=p.index := by
  by_contra hne
  have hd := disjoint hne
  change Disjoint (geometry o.index).interior (geometry p.index).interior at hd
  rw [← o.transport.interior,← p.transport.interior] at hd
  have he : o.triangle.interior=p.triangle.interior := by
    change OpenTriangle o.triangle.p o.triangle.q o.triangle.r=
      OpenTriangle p.triangle.p p.triangle.q p.triangle.r
    rw [o.center,o.left,o.right,p.center,p.left,p.right]
  rw [he] at hd
  obtain ⟨x,hx⟩ := interior_nonempty p.triangle
  exact Set.disjoint_left.mp hd hx hx

theorem adjacent_indices_ne {α : Type*} (geometry : α → TriangleGeometry)
    {r : ℕ} [NeZero (2*r)] (hr : 2≤r) (c : Point) (P : ZMod (2*r) → Point)
    (pinj : Function.Injective P) (pne : ∀ z, P z≠c)
    (z : ZMod (2*r)) (o : Occurrence geometry c P (z-1))
    (p : Occurrence geometry c P z) : o.index≠p.index := by
  intro he
  exact cyclic_previous_ne r hr z (occurrence_index_injective geometry hr c P pinj pne o p he)

/-- Actual two-sided sharing follows from the two original certificate
indices retained by adjacent occupied sectors. -/
theorem shared_of_adjacent_occurrences {α : Type*} [Fintype α]
    (geometry : α → TriangleGeometry)
    (disjoint : Pairwise (fun a b => Disjoint (geometry a).interior (geometry b).interior))
    {r : ℕ} [NeZero (2*r)] (hr : 2≤r) (c : Point) (P : ZMod (2*r) → Point)
    (pinj : Function.Injective P) (pne : ∀ z, P z≠c)
    (z : ZMod (2*r)) (o : Occurrence geometry c P (z-1))
    (p : Occurrence geometry c P z) : {c,P z}∈sharedEdges geometry := by
  classical
  have hn := adjacent_indices_ne geometry hr c P pinj pne z o p
  obtain ⟨i,hi⟩ := o.transport.sides 2
  obtain ⟨j,hj⟩ := p.transport.sides 0
  have ho : sideMap geometry (o.index,i)={c,P z} := by
    rw [sideMap,← hi]
    simp [edge,sideTriangle,cycle,o.center,o.right,pair_comm]
  have hp : sideMap geometry (p.index,j)={c,P z} := by
    rw [sideMap,← hj]
    simp [edge,sideTriangle,p.center,p.left]
  have hij : (o.index,i)≠(p.index,j) := by
    intro he
    exact hn (congrArg Prod.fst he)
  let F := (univ : Finset (α × Fin 3)).filter (fun a => sideMap geometry a={c,P z})
  have hsub : {(o.index,i),(p.index,j)}⊆F := by
    intro a ha
    simp only [mem_insert,mem_singleton] at ha
    rcases ha with rfl|rfl <;> apply mem_filter.mpr
    · exact ⟨mem_univ _,ho⟩
    · exact ⟨mem_univ _,hp⟩
  have hcard := card_le_card hsub
  rw [card_pair hij] at hcard
  have hge : 2≤degree geometry {c,P z} := hcard
  have hle := degree_le_two geometry disjoint {c,P z}
  exact mem_filter.mpr ⟨mem_image.mpr ⟨(p.index,j),mem_univ _,hp⟩,by omega⟩

#print axioms occurrence_index_injective
#print axioms shared_of_adjacent_occurrences
end Kobon.UpperOpenMathSectorIncidence
