import Kobon.UpperOpenMathRadialOrder
import Kobon.UpperCleanEdges
import Kobon.UpperCleanPairing

/-!
# Actual first vertices and auxiliary points on unbounded rays

Each canonical ray receives its unique incident elementary edge endpoint if
there is any actual arrangement vertex on that ray. Otherwise it receives a
positive auxiliary point. This avoids the false premise that every ray has
a first actual vertex. Positive orientation, antipodality, and injectivity
are preserved by the independent positive ray lengths.
-/
namespace Kobon.UpperOpenMathRadialOrder
open Cells UpperVertexBudget UpperEdgeInventory UpperOpenMathRadialOrder Finset

namespace OrderedDirections
variable {n : ℕ} {L : ℕ → Line ℝ} {S : Finset (Fin n)}
  (D : UpperOpenMathRadialOrder.OrderedDirections n L S)
  [NeZero (2*S.card)]

noncomputable def rayCut (c : Point) (z : ZMod (2*S.card)) : Line ℝ :=
  if z.val<S.card then ⟨1,D.parameter,c.1+D.parameter*c.2⟩ else
    ⟨-1,-D.parameter,-(c.1+D.parameter*c.2)⟩

omit [NeZero (2*S.card)] in
@[simp] theorem rayCut_center (c : Point) (z : ZMod (2*S.card)) :
    affineEval (D.rayCut c z) c=0 := by
  unfold rayCut
  split_ifs <;> dsimp [affineEval] <;> ring

theorem rayCut_point (c : Point) (z : ZMod (2*S.card)) (scale : ℝ) :
    affineEval (D.rayCut c z) (D.cyclicPoint c z scale)=scale := by
  have ht := D.cyclicVector_transverse z
  unfold rayCut
  split_ifs with h
  · simp only [h,ite_true] at ht
    have hm := congrArg (fun x : ℝ => scale*x) ht
    dsimp [cyclicPoint,affineEval]
    nlinarith [hm]
  · simp only [h,ite_false] at ht
    have hm := congrArg (fun x : ℝ => scale*x) ht
    dsimp [cyclicPoint,affineEval]
    nlinarith [hm]

theorem rayCut_det (c : Point) (z : ZMod (2*S.card)) :
    det (L (D.cyclicRadial z)) (D.rayCut c z)≠0 := by
  have hn := D.nonzero (D.cyclicRadial z)
  unfold rayCut
  split_ifs
  all_goals
    dsimp [det,transverse] at *
    intro he
    apply hn
    nlinarith

theorem point_reconstruction (c : Point)
    (hc : ∀ i∈S, affineEval (L i) c=0)
    (z : ZMod (2*S.card)) (p : Point)
    (hp : affineEval (L (D.cyclicRadial z)) p=0) :
    D.cyclicPoint c z (affineEval (D.rayCut c z) p)=p := by
  let q := D.cyclicPoint c z (affineEval (D.rayCut c z) p)
  let w := D.rayCut c z
  let shifted : Line ℝ := ⟨w.a,w.b,w.c+affineEval w p⟩
  have hdet : det (L (D.cyclicRadial z)) shifted≠0 := D.rayCut_det c z
  apply two_lines_two_points (L (D.cyclicRadial z)) shifted q p hdet
  · exact D.cyclicPoint_on_line c hc z _
  · exact hp
  · have hq := D.rayCut_point c z (affineEval w p)
    dsimp [q,w,shifted,affineEval] at *
    linarith
  · dsimp [shifted,affineEval]
    ring

noncomputable def BoundedRay (c : Point) (z : ZMod (2*S.card)) : Prop :=
  ∃ q∈onLine n L (D.cyclicRadial z), 0<affineEval (D.rayCut c z) q

theorem first_endpoint_exists (hL : NoParallel n L) (hn : 2≤n)
    (c : Point) (hc : c∈vertices n L)
    (hinc : ∀ i∈S, affineEval (L i) c=0)
    (z : ZMod (2*S.card)) (bounded : D.BoundedRay c z) :
    ∃ q : Point, q∈onLine n L (D.cyclicRadial z) ∧
      {c,q}∈lineEdges n L (D.cyclicRadial z) ∧ 0<affineEval (D.rayCut c z) q := by
  obtain ⟨p,hp,hpos⟩ := bounded
  exact UpperCleanEdges.incident_positive_edge n L hL hn (D.cyclicRadial z)
    (D.rayCut c z) c p (mem_filter.mpr ⟨hc,hinc _ (D.cyclicRadial_mem z)⟩)
    hp (D.rayCut_center c z) hpos

noncomputable def firstEndpoint (hL : NoParallel n L) (hn : 2≤n)
    (c : Point) (hc : c∈vertices n L)
    (hinc : ∀ i∈S, affineEval (L i) c=0)
    (z : ZMod (2*S.card)) (bounded : D.BoundedRay c z) : Point :=
  Classical.choose (D.first_endpoint_exists hL hn c hc hinc z bounded)

theorem firstEndpoint_spec (hL : NoParallel n L) (hn : 2≤n)
    (c : Point) (hc : c∈vertices n L)
    (hinc : ∀ i∈S, affineEval (L i) c=0)
    (z : ZMod (2*S.card)) (bounded : D.BoundedRay c z) :
    D.firstEndpoint hL hn c hc hinc z bounded∈onLine n L (D.cyclicRadial z) ∧
      {c,D.firstEndpoint hL hn c hc hinc z bounded}∈lineEdges n L (D.cyclicRadial z) ∧
      0<affineEval (D.rayCut c z) (D.firstEndpoint hL hn c hc hinc z bounded) :=
  Classical.choose_spec (D.first_endpoint_exists hL hn c hc hinc z bounded)

noncomputable def rayScale (hL : NoParallel n L) (hn : 2≤n)
    (c : Point) (hc : c∈vertices n L)
    (hinc : ∀ i∈S, affineEval (L i) c=0) (z : ZMod (2*S.card)) : ℝ := by
  classical
  exact if h : D.BoundedRay c z then
    affineEval (D.rayCut c z) (D.firstEndpoint hL hn c hc hinc z h) else 1

theorem rayScale_positive (hL : NoParallel n L) (hn : 2≤n)
    (c : Point) (hc : c∈vertices n L)
    (hinc : ∀ i∈S, affineEval (L i) c=0) (z : ZMod (2*S.card)) :
    0<D.rayScale hL hn c hc hinc z := by
  classical
  unfold rayScale
  split_ifs with h
  · exact (D.firstEndpoint_spec hL hn c hc hinc z h).2.2
  · norm_num

noncomputable def rayPoint (hL : NoParallel n L) (hn : 2≤n)
    (c : Point) (hc : c∈vertices n L)
    (hinc : ∀ i∈S, affineEval (L i) c=0) (z : ZMod (2*S.card)) : Point :=
  D.cyclicPoint c z (D.rayScale hL hn c hc hinc z)

theorem rayPoint_on_line (hL : NoParallel n L) (hn : 2≤n)
    (c : Point) (hc : c∈vertices n L)
    (hinc : ∀ i∈S, affineEval (L i) c=0) (z : ZMod (2*S.card)) :
    affineEval (L (D.cyclicRadial z)) (D.rayPoint hL hn c hc hinc z)=0 :=
  D.cyclicPoint_on_line c hinc z _

theorem rayPoint_of_bounded (hL : NoParallel n L) (hn : 2≤n)
    (c : Point) (hc : c∈vertices n L)
    (hinc : ∀ i∈S, affineEval (L i) c=0)
    (z : ZMod (2*S.card)) (bounded : D.BoundedRay c z) :
    D.rayPoint hL hn c hc hinc z=D.firstEndpoint hL hn c hc hinc z bounded := by
  classical
  unfold rayPoint rayScale
  rw [dif_pos bounded]
  apply D.point_reconstruction c hinc z
  exact (mem_filter.mp (D.firstEndpoint_spec hL hn c hc hinc z bounded).1).2

theorem rayPoint_inventory (hL : NoParallel n L) (hn : 2≤n)
    (c : Point) (hc : c∈vertices n L)
    (hinc : ∀ i∈S, affineEval (L i) c=0)
    (z : ZMod (2*S.card)) (bounded : D.BoundedRay c z) :
    D.rayPoint hL hn c hc hinc z∈onLine n L (D.cyclicRadial z) ∧
      {c,D.rayPoint hL hn c hc hinc z}∈lineEdges n L (D.cyclicRadial z) := by
  rw [D.rayPoint_of_bounded hL hn c hc hinc z bounded]
  exact ⟨(D.firstEndpoint_spec hL hn c hc hinc z bounded).1,
    (D.firstEndpoint_spec hL hn c hc hinc z bounded).2.1⟩

/-- Any actual elementary side on the same ray has the selected endpoint.
This proves the consistency needed when two adjacent triangular sectors
share a radial side. -/
theorem rayPoint_eq_of_incident_edge (hL : NoParallel n L) (hn : 2≤n)
    (c : Point) (hc : c∈vertices n L)
    (hinc : ∀ i∈S, affineEval (L i) c=0)
    (z : ZMod (2*S.card)) (q : Point)
    (hq : q∈onLine n L (D.cyclicRadial z))
    (hedge : {c,q}∈lineEdges n L (D.cyclicRadial z))
    (positive : 0<affineEval (D.rayCut c z) q) :
    D.rayPoint hL hn c hc hinc z=q := by
  have bounded : D.BoundedRay c z := ⟨q,hq,positive⟩
  obtain ⟨hr,her⟩ := D.rayPoint_inventory hL hn c hc hinc z bounded
  apply UpperCleanPairing.incident_positive_unique n L hL hn (D.cyclicRadial z)
    (D.rayCut c z) c _ q
    (mem_filter.mpr ⟨hc,hinc _ (D.cyclicRadial_mem z)⟩) hr hq her hedge
    (D.rayCut_center c z)
  · rw [rayPoint,D.rayCut_point]
    exact D.rayScale_positive hL hn c hc hinc z
  · exact positive

theorem rayPoint_positive_orientation (hL : NoParallel n L) (hn : 2≤n)
    (hr : 2≤S.card) (c : Point) (hc : c∈vertices n L)
    (hinc : ∀ i∈S, affineEval (L i) c=0) (z : ZMod (2*S.card)) :
    0<areaDet c (D.rayPoint hL hn c hc hinc z) (D.rayPoint hL hn c hc hinc (z+1)) :=
  D.cyclicPoint_consecutive_positive hr c z _ _
    (D.rayScale_positive hL hn c hc hinc z)
    (D.rayScale_positive hL hn c hc hinc (z+1))

theorem rayPoint_antipodal (hL : NoParallel n L) (hn : 2≤n)
    (hr : 2≤S.card) (c : Point) (hc : c∈vertices n L)
    (hinc : ∀ i∈S, affineEval (L i) c=0) (z : ZMod (2*S.card)) :
    ∃ v : ℝ, 0<v ∧ D.rayPoint hL hn c hc hinc (z+(S.card : ZMod (2*S.card)))=
      (c.1-v*((D.rayPoint hL hn c hc hinc z).1-c.1),
       c.2-v*((D.rayPoint hL hn c hc hinc z).2-c.2)) :=
  D.cyclicPoint_antipodal hr c (D.rayScale hL hn c hc hinc)
    (D.rayScale_positive hL hn c hc hinc) z

theorem rayPoint_injective (hL : NoParallel n L) (hn : 2≤n)
    (hr : 2≤S.card) (c : Point) (hc : c∈vertices n L)
    (hinc : ∀ i∈S, affineEval (L i) c=0) :
    Function.Injective (D.rayPoint hL hn c hc hinc) :=
  D.cyclicPoint_injective hr c hinc hL (D.rayScale hL hn c hc hinc)
    (D.rayScale_positive hL hn c hc hinc)

theorem first_half_radial (k : Fin S.card) :
    D.cyclicRadial (k.val : ZMod (2*S.card))=D.radial k := by
  have hv : (k.val : ZMod (2*S.card)).val=k.val := ZMod.val_natCast_of_lt (by have := k.isLt; omega)
  unfold cyclicRadial
  simp only [hv,dif_pos k.isLt]

theorem opposite_half_radial (k : Fin S.card) :
    D.cyclicRadial ((k.val+S.card : ℕ) : ZMod (2*S.card))=D.radial k := by
  have hv : ((k.val+S.card : ℕ) : ZMod (2*S.card)).val=k.val+S.card :=
    ZMod.val_natCast_of_lt (by have := k.isLt; omega)
  have hn : ¬k.val+S.card<S.card := by omega
  unfold cyclicRadial
  rw [dif_neg (by rw [hv]; exact hn)]
  simp only [hv,Nat.add_sub_cancel]

omit [NeZero (2*S.card)] in
theorem first_half_cut (c : Point) (k : Fin S.card) :
    D.rayCut c (k.val : ZMod (2*S.card))=⟨1,D.parameter,c.1+D.parameter*c.2⟩ := by
  have hv : (k.val : ZMod (2*S.card)).val=k.val := ZMod.val_natCast_of_lt (by have := k.isLt; omega)
  simp [rayCut,hv,k.isLt]

omit [NeZero (2*S.card)] in
theorem opposite_half_cut (c : Point) (k : Fin S.card) :
    D.rayCut c ((k.val+S.card : ℕ) : ZMod (2*S.card))=
      ⟨-1,-D.parameter,-(c.1+D.parameter*c.2)⟩ := by
  have hv : ((k.val+S.card : ℕ) : ZMod (2*S.card)).val=k.val+S.card :=
    ZMod.val_natCast_of_lt (by have := k.isLt; omega)
  have hn : ¬k.val+S.card<S.card := by omega
  unfold rayCut
  rw [if_neg (by rw [hv]; exact hn)]

/-- Every actual elementary edge incident to the selected vertex has a
unique ray index in the canonical cyclic assignment. This is a geometric
surjectivity theorem, rather than an assumed ray-to-edge association. -/
theorem incident_edge_has_ray (hL : NoParallel n L) (hn : 2≤n)
    (c : Point) (hc : c∈vertices n L)
    (hinc : ∀ i∈S, affineEval (L i) c=0)
    (i : Fin n) (hi : i∈S) (q : Point)
    (hq : q∈onLine n L i) (hqc : q≠c) (hedge : {c,q}∈lineEdges n L i) :
    ∃ z : ZMod (2*S.card), D.cyclicRadial z=i ∧ D.rayPoint hL hn c hc hinc z=q := by
  obtain ⟨k,hk⟩ := D.radial_surjective i hi
  let z : ZMod (2*S.card) := k.val
  have hz : D.cyclicRadial z=i := (D.first_half_radial k).trans hk
  have hzero : affineEval (D.rayCut c z) q≠0 := by
    intro he
    apply hqc
    exact two_lines_two_points (L (D.cyclicRadial z)) (D.rayCut c z) q c
      (D.rayCut_det c z)
      (by rw [hz]; exact (mem_filter.mp hq).2)
      (hinc _ (D.cyclicRadial_mem z)) he (D.rayCut_center c z)
  rcases lt_or_gt_of_ne hzero with hneg|hpos
  · let w : ZMod (2*S.card) := ((k.val+S.card : ℕ) : ZMod (2*S.card))
    have hw : D.cyclicRadial w=i := (D.opposite_half_radial k).trans hk
    have hcut : affineEval (D.rayCut c w) q= -affineEval (D.rayCut c z) q := by
      rw [D.opposite_half_cut c k,D.first_half_cut c k]
      dsimp [affineEval]
      ring
    refine ⟨w,hw,?_⟩
    apply D.rayPoint_eq_of_incident_edge hL hn c hc hinc w q
    · simpa only [hw] using hq
    · simpa only [hw] using hedge
    · rw [hcut]
      linarith
  · refine ⟨z,hz,?_⟩
    apply D.rayPoint_eq_of_incident_edge hL hn c hc hinc z q
    · simpa only [hz] using hq
    · simpa only [hz] using hedge
    · exact hpos

end OrderedDirections

#print axioms OrderedDirections.rayPoint_eq_of_incident_edge
#print axioms OrderedDirections.rayPoint_positive_orientation
#print axioms OrderedDirections.rayPoint_antipodal
#print axioms OrderedDirections.rayPoint_injective
#print axioms OrderedDirections.incident_edge_has_ray
end Kobon.UpperOpenMathRadialOrder
