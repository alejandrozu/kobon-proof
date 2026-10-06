import Kobon.UpperOpenMathSectorIncidence

/-!
# Matching adjacent sector records through their actual side fibers

Original certificate indices and geometric orientation identify the two
triangles on a shared edge in both local charts. The neighboring endpoints
then agree. This removes the previously assumed fan-matching equations when
the local charts have been extracted from the same actual triangle family.
-/
namespace Kobon.UpperOpenMathFiberMatching
open Cells UpperTriangleIncidence UpperOpenMathAlignedTriangles
  UpperOpenMathSectorRecords UpperOpenMathSectorIncidence Finset

theorem third_vertex_eq_reversed_base (s t : TriangleGeometry)
    (hp : t.p=s.q) (hq : t.q=s.p)
    (hv : triangleVertices s=triangleVertices t) : s.r=t.r := by
  classical
  have hrp : s.r≠s.p := by intro h; apply s.Ap; simpa only [h] using s.Ar
  have hrq : s.r≠s.q := by intro h; apply s.Bq; simpa only [h] using s.Br
  have hm : s.r∈triangleVertices t := by rw [← hv]; simp [triangleVertices]
  simp only [triangleVertices,hp,hq,mem_insert,mem_singleton] at hm
  exact hm.resolve_left hrq |>.resolve_left hrp

theorem positive_reversed_base_indices_ne {α : Type*}
    (geometry : α → TriangleGeometry) (a b : α) (s t : TriangleGeometry)
    (hs : Transport s (geometry a)) (ht : Transport t (geometry b))
    (hp : t.p=s.q) (hq : t.q=s.p)
    (ps : 0<areaDet s.p s.q s.r) (pt : 0<areaDet t.p t.q t.r) : a≠b := by
  intro hab
  have hv : triangleVertices s=triangleVertices t := by
    rw [hs.vertices,ht.vertices,hab]
  have hr := third_vertex_eq_reversed_base s t hp hq hv
  have he : areaDet t.p t.q t.r= -areaDet s.p s.q s.r := by
    rw [hp,hq,← hr]
    dsimp [areaDet]
    ring
  rw [he] at pt
  linarith

theorem no_three_origins_on_edge {α : Type*} [Fintype α]
    (geometry : α → TriangleGeometry)
    (disjoint : Pairwise (fun a b => Disjoint (geometry a).interior (geometry b).interior))
    (a b c : α) (ab : a≠b) (ac : a≠c) (bc : b≠c) (e : Edge)
    (ha : ∃ i : Fin 3, edge (geometry a) i=e)
    (hb : ∃ j : Fin 3, edge (geometry b) j=e)
    (hc : ∃ k : Fin 3, edge (geometry c) k=e) : False := by
  classical
  obtain ⟨i,hi⟩ := ha
  obtain ⟨j,hj⟩ := hb
  obtain ⟨k,hk⟩ := hc
  have hij : (a,i)≠(b,j) := fun he => ab (congrArg Prod.fst he)
  have hik : (a,i)≠(c,k) := fun he => ac (congrArg Prod.fst he)
  have hjk : (b,j)≠(c,k) := fun he => bc (congrArg Prod.fst he)
  let S := (univ : Finset (α × Fin 3)).filter (fun p => sideMap geometry p=e)
  have hsub : {(a,i),(b,j),(c,k)}⊆S := by
    intro p hp
    simp only [mem_insert,mem_singleton] at hp
    rcases hp with rfl|rfl|rfl <;> apply mem_filter.mpr
    · exact ⟨mem_univ _,hi⟩
    · exact ⟨mem_univ _,hj⟩
    · exact ⟨mem_univ _,hk⟩
  have hcard := card_le_card hsub
  have ht : ({(a,i),(b,j),(c,k)} : Finset (α × Fin 3)).card=3 := by simp [hij,hik,hjk]
  rw [ht] at hcard
  have hthree : 3≤degree geometry e := hcard
  have htwo := degree_le_two geometry disjoint e
  omega

theorem transported_edge_origin {α : Type*} (geometry : α → TriangleGeometry)
    (a : α) (t : TriangleGeometry) (ht : Transport t (geometry a))
    (i : Fin 3) (e : Edge) (he : edge t i=e) :
    ∃ j : Fin 3, edge (geometry a) j=e := by
  obtain ⟨j,hj⟩ := ht.sides i
  exact ⟨j,hj.symm.trans he⟩

section Matching
variable {α : Type*} [Fintype α]
  (geometry : α → TriangleGeometry)
  (disjoint : Pairwise (fun a b => Disjoint (geometry a).interior (geometry b).interior))
  {r s : ℕ} [NeZero (2*r)] [NeZero (2*s)]
  (hr : 2≤r) (hs : 2≤s) (c d : Point)
  (P : ZMod (2*r) → Point) (Q : ZMod (2*s) → Point)
  (pinj : Function.Injective P) (qinj : Function.Injective Q)
  (pne : ∀ z, P z≠c) (qne : ∀ z, Q z≠d)
  (ppos : ∀ z, 0<areaDet c (P z) (P (z+1)))
  (qpos : ∀ z, 0<areaDet d (Q z) (Q (z+1)))
  (z : ZMod (2*r)) (w : ZMod (2*s))
  (hd : d=P z) (hc : Q w=c)
  (o : Occurrence geometry c P (z-1)) (p : Occurrence geometry c P z)
  (a : Occurrence geometry d Q (w-1)) (b : Occurrence geometry d Q w)

include disjoint hr hs pinj qinj pne qne ppos qpos hd hc o p a b

theorem neighboring_original_indices : p.index=a.index ∧ o.index=b.index := by
  classical
  let e : Edge := {c,d}
  have op : o.index≠p.index := adjacent_indices_ne geometry hr c P pinj pne z o p
  have ab : a.index≠b.index := adjacent_indices_ne geometry hs d Q qinj qne w a b
  have pb : p.index≠b.index := by
    apply positive_reversed_base_indices_ne geometry p.index b.index p.triangle b.triangle
      p.transport b.transport
    · rw [b.center,p.left,hd]
    · rw [b.left,p.center,hc]
    · simpa only [p.center,p.left,p.right] using ppos z
    · simpa only [b.center,b.left,b.right] using qpos w
  have origin_o : ∃ i : Fin 3, edge (geometry o.index) i=e := by
    apply transported_edge_origin geometry o.index o.triangle o.transport 2 e
    simp [edge,sideTriangle,cycle,o.center,o.right,hd,pair_comm,e]
  have origin_p : ∃ i : Fin 3, edge (geometry p.index) i=e := by
    apply transported_edge_origin geometry p.index p.triangle p.transport 0 e
    simp [edge,sideTriangle,p.center,p.left,hd,e]
  have origin_a : ∃ i : Fin 3, edge (geometry a.index) i=e := by
    apply transported_edge_origin geometry a.index a.triangle a.transport 2 e
    simp [edge,sideTriangle,cycle,a.center,a.right,hc,pair_comm,e]
  have origin_b : ∃ i : Fin 3, edge (geometry b.index) i=e := by
    apply transported_edge_origin geometry b.index b.triangle b.transport 0 e
    simp [edge,sideTriangle,b.center,b.left,hc,pair_comm,e]
  have pa : p.index=a.index := by
    by_contra hpa
    exact no_three_origins_on_edge geometry disjoint p.index a.index b.index
      hpa pb ab e origin_p origin_a origin_b
  have ob : o.index=b.index := by
    by_contra hob
    exact no_three_origins_on_edge geometry disjoint o.index p.index b.index
      op hob pb e origin_o origin_p origin_b
  exact ⟨pa,ob⟩

/-- The formerly assumed neighboring endpoint equations are consequences
of actual side occurrence capacity, preserved original triangle identities,
and the positive orientations of the two local charts. -/
theorem neighboring_points_match : Q (w-1)=P (z+1) ∧ Q (w+1)=P (z-1) := by
  classical
  obtain ⟨pa,ob⟩ := neighboring_original_indices geometry disjoint hr hs c d P Q
    pinj qinj pne qne ppos qpos z w hd hc o p a b
  have hpv : triangleVertices p.triangle=triangleVertices a.triangle := by
    rw [p.transport.vertices,a.transport.vertices,pa]
  have hov : triangleVertices o.triangle=triangleVertices b.triangle := by
    rw [o.transport.vertices,b.transport.vertices,ob]
  have prc : p.triangle.r≠c := by
    intro h
    apply p.triangle.Ap
    simpa only [h,← p.center] using p.triangle.Ar
  have prd : p.triangle.r≠d := by
    intro h
    apply p.triangle.Bq
    have hpq : p.triangle.q=d := p.left.trans hd.symm
    simpa only [hpq] using (h ▸ p.triangle.Br)
  have oqc : o.triangle.q≠c := by
    simpa only [o.left] using pne (z-1)
  have oqd : o.triangle.q≠d := by
    intro h
    apply o.triangle.Bq
    have hor : o.triangle.r=d := by
      have hoz : o.triangle.r=P z := by simpa only [sub_add_cancel] using o.right
      exact hoz.trans hd.symm
    simpa only [h,hor] using o.triangle.Br
  constructor
  · have hm : p.triangle.r∈triangleVertices a.triangle := by rw [← hpv]; simp [triangleVertices]
    simp only [triangleVertices,a.center,a.left,a.right,sub_add_cancel,hc,
      mem_insert,mem_singleton] at hm
    have hmatch : p.triangle.r=Q (w-1) := hm.resolve_left prd |>.resolve_right prc
    simpa only [p.right] using hmatch.symm
  · have hm : o.triangle.q∈triangleVertices b.triangle := by rw [← hov]; simp [triangleVertices]
    simp only [triangleVertices,b.center,b.left,b.right,hc,mem_insert,mem_singleton] at hm
    have hmatch : o.triangle.q=Q (w+1) := hm.resolve_left oqd |>.resolve_left oqc
    simpa only [o.left] using hmatch.symm

end Matching

#print axioms no_three_origins_on_edge
#print axioms neighboring_points_match
end Kobon.UpperOpenMathFiberMatching
