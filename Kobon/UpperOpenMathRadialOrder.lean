import Kobon.UpperCoreExtraction
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Data.ZMod.Basic

/-!
# Canonical half-plane ordering of actual incident line directions

A generic transverse linear functional is nonzero on every indexed line
direction. Normalize each direction to functional value one and sort its
second coordinate. Nonparallelness makes these coordinates distinct. The
resulting order contains every actual incident line exactly once and gives
positive determinants between every pair of increasing representatives.

This closes the half-plane sorting portion of cyclic fan extraction. It
does not yet identify first vertices, triangles occupying sectors, or global
shared-edge incidence equivalences.
-/
namespace Kobon.UpperOpenMathRadialOrder
open Cells UpperVertexBudget Finset

noncomputable def transverse (t : ℝ) (l : Line ℝ) : ℝ := l.b-t*l.a

theorem exists_transverse (n : ℕ) (L : ℕ → Line ℝ)
    (hL : NoParallel n L) (hn : 2≤n) :
    ∃ t : ℝ, ∀ i : Fin n, transverse t (L i)≠0 := by
  classical
  let bad : Finset ℝ := (univ.filter (fun i : Fin n => (L i).a≠0)).image
    (fun i : Fin n => (L i).b/(L i).a)
  obtain ⟨t,ht⟩ := bad.exists_notMem
  refine ⟨t,?_⟩
  intro i he
  by_cases ha : (L i).a=0
  · have hv := line_valid n L hL hn i
    have hb : (L i).b≠0 := hv.resolve_left (not_not.mpr ha)
    exact hb (by simpa only [transverse,ha,mul_zero,sub_zero] using he)
  · apply ht
    apply mem_image.mpr
    refine ⟨i,mem_filter.mpr ⟨mem_univ i,ha⟩,?_⟩
    apply (div_eq_iff ha).mpr
    dsimp [transverse] at he
    linarith

noncomputable def slope (t : ℝ) (l : Line ℝ) : ℝ := -l.a/transverse t l

noncomputable def direction (t : ℝ) (l : Line ℝ) : Point :=
  (l.b/transverse t l,-l.a/transverse t l)

theorem direction_normalized (t : ℝ) (l : Line ℝ) (h : transverse t l≠0) :
    (direction t l).1+t*(direction t l).2=1 := by
  dsimp [direction,transverse] at *
  field_simp
  ring

theorem direction_on_line (t : ℝ) (l : Line ℝ) :
    l.a*(direction t l).1+l.b*(direction t l).2=0 := by
  dsimp [direction]
  ring

theorem slope_injective (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L)
    (t : ℝ) (ht : ∀ i : Fin n, transverse t (L i)≠0) :
    Function.Injective (fun i : Fin n => slope t (L i)) := by
  intro i j he
  by_contra hij
  have hd : det (L i) (L j)≠0 := noParallel_any n L hL i j i.isLt j.isLt
    (fun h => hij (Fin.ext h))
  apply hd
  dsimp [slope] at he
  have hc := (div_eq_div_iff (ht i) (ht j)).mp he
  dsimp [transverse,det] at hc ⊢
  nlinarith

/-- Every selected line occurs exactly once in the ordered representatives.
The positivity statement covers all increasing pairs, not only consecutive
ones, preventing an artificial multiple winding of the radial enumeration. -/
structure OrderedDirections (n : ℕ) (L : ℕ → Line ℝ)
    (S : Finset (Fin n)) where
  parameter : ℝ
  radial : Fin S.card → Fin n
  radial_mem : ∀ k, radial k∈S
  radial_injective : Function.Injective radial
  radial_surjective : ∀ i∈S, ∃ k, radial k=i
  nonzero : ∀ i : Fin n, transverse parameter (L i)≠0
  increasing : StrictMono (fun k => slope parameter (L (radial k)))

noncomputable def orderedDirections (n : ℕ) (L : ℕ → Line ℝ)
    (hL : NoParallel n L) (hn : 2≤n) (S : Finset (Fin n)) :
    OrderedDirections n L S := by
  classical
  let t := Classical.choose (exists_transverse n L hL hn)
  have ht := Classical.choose_spec (exists_transverse n L hL hn)
  let values := S.image (fun i : Fin n => slope t (L i))
  have hcard : values.card=S.card := card_image_of_injective S (slope_injective n L hL t ht)
  have hex (k : Fin S.card) : ∃ i∈S,
      slope t (L i)=values.orderEmbOfFin hcard k := by
    exact mem_image.mp (values.orderEmbOfFin_mem hcard k)
  choose radial hm he using hex
  refine ⟨t,radial,hm,?_,?_,ht,?_⟩
  · intro a b hab
    apply (values.orderEmbOfFin hcard).injective
    rw [← he a,← he b,hab]
  · intro i hi
    let x : values := ⟨slope t (L i),mem_image.mpr ⟨i,hi,rfl⟩⟩
    let k := (values.orderIsoOfFin hcard).symm x
    refine ⟨k,?_⟩
    apply slope_injective n L hL t ht
    change slope t (L (radial k))=slope t (L i)
    rw [he k]
    change ((values.orderIsoOfFin hcard) k).val=x.val
    rw [(values.orderIsoOfFin hcard).apply_symm_apply]
  · intro a b hab
    change slope t (L (radial a))<slope t (L (radial b))
    rw [he a,he b]
    exact (values.orderEmbOfFin hcard).strictMono hab

namespace OrderedDirections
variable {n : ℕ} {L : ℕ → Line ℝ} {S : Finset (Fin n)}
  (D : OrderedDirections n L S)

noncomputable def vector (k : Fin S.card) : Point := direction D.parameter (L (D.radial k))

theorem vector_ne_zero (k : Fin S.card) : D.vector k≠(0,0) := by
  intro he
  have hn := direction_normalized D.parameter (L (D.radial k)) (D.nonzero (D.radial k))
  change (D.vector k).1+D.parameter*(D.vector k).2=1 at hn
  rw [he] at hn
  norm_num at hn

theorem vector_det (a b : Fin S.card) :
    (D.vector a).1*(D.vector b).2-(D.vector a).2*(D.vector b).1=
      slope D.parameter (L (D.radial b))-slope D.parameter (L (D.radial a)) := by
  have ha := direction_normalized D.parameter (L (D.radial a)) (D.nonzero (D.radial a))
  have hb := direction_normalized D.parameter (L (D.radial b)) (D.nonzero (D.radial b))
  change (D.vector a).1+D.parameter*(D.vector a).2=1 at ha
  change (D.vector b).1+D.parameter*(D.vector b).2=1 at hb
  have he₁ : (D.vector a).2=slope D.parameter (L (D.radial a)) := rfl
  have he₂ : (D.vector b).2=slope D.parameter (L (D.radial b)) := rfl
  rw [← he₁,← he₂]
  have hma := congrArg (fun x : ℝ => x*(D.vector b).2) ha
  have hmb := congrArg (fun x : ℝ => x*(D.vector a).2) hb
  nlinarith [hma,hmb]

theorem vector_det_positive {a b : Fin S.card} (hab : a<b) :
    0<(D.vector a).1*(D.vector b).2-(D.vector a).2*(D.vector b).1 := by
  rw [D.vector_det]
  exact sub_pos.mpr (D.increasing hab)

noncomputable def outerPoint (c : Point) (k : Fin S.card) (scale : ℝ) : Point :=
  (c.1+scale*(D.vector k).1,c.2+scale*(D.vector k).2)

theorem outerPoint_on_line (c : Point)
    (hc : ∀ i∈S, affineEval (L i) c=0) (k : Fin S.card) (scale : ℝ) :
    affineEval (L (D.radial k)) (D.outerPoint c k scale)=0 := by
  have hcenter := hc (D.radial k) (D.radial_mem k)
  have hd := direction_on_line D.parameter (L (D.radial k))
  change (L (D.radial k)).a*(D.vector k).1+(L (D.radial k)).b*(D.vector k).2=0 at hd
  dsimp [outerPoint,affineEval] at *
  have hm := congrArg (fun x : ℝ => scale*x) hd
  nlinarith [hm]

theorem outerPoint_area (c : Point) (a b : Fin S.card) (u v : ℝ) :
    areaDet c (D.outerPoint c a u) (D.outerPoint c b v)=
      u*v*((D.vector a).1*(D.vector b).2-(D.vector a).2*(D.vector b).1) := by
  dsimp [outerPoint,areaDet]
  ring

theorem outerPoint_area_positive (c : Point) {a b : Fin S.card}
    (hab : a<b) (u v : ℝ) (hu : 0<u) (hv : 0<v) :
    0<areaDet c (D.outerPoint c a u) (D.outerPoint c b v) := by
  rw [D.outerPoint_area]
  exact mul_pos (mul_pos hu hv) (D.vector_det_positive hab)

section Cyclic
variable [NeZero (2*S.card)]

noncomputable def cyclicVector (z : ZMod (2*S.card)) : Point :=
  if h : z.val<S.card then D.vector ⟨z.val,h⟩ else
    let k : Fin S.card := ⟨z.val-S.card,by have := ZMod.val_lt z; omega⟩
    (-((D.vector k).1),-((D.vector k).2))

noncomputable def cyclicRadial (z : ZMod (2*S.card)) : Fin n :=
  if h : z.val<S.card then D.radial ⟨z.val,h⟩ else
    D.radial ⟨z.val-S.card,by have := ZMod.val_lt z; omega⟩

theorem cyclicRadial_mem (z : ZMod (2*S.card)) : D.cyclicRadial z∈S := by
  unfold cyclicRadial
  split_ifs <;> exact D.radial_mem _

theorem cyclicVector_on_line (z : ZMod (2*S.card)) :
    (L (D.cyclicRadial z)).a*(D.cyclicVector z).1+
      (L (D.cyclicRadial z)).b*(D.cyclicVector z).2=0 := by
  unfold cyclicRadial cyclicVector
  split_ifs with h
  · exact direction_on_line D.parameter (L (D.radial ⟨z.val,h⟩))
  · have hd := direction_on_line D.parameter
      (L (D.radial ⟨z.val-S.card,by have := ZMod.val_lt z; omega⟩))
    change (L _).a*(-(D.vector _).1)+(L _).b*(-(D.vector _).2)=0
    change (L _).a*(D.vector _).1+(L _).b*(D.vector _).2=0 at hd
    nlinarith

theorem cyclicVector_antipodal (hr : 2≤S.card) (z : ZMod (2*S.card)) :
    D.cyclicVector (z+(S.card : ZMod (2*S.card)))=
      (-((D.cyclicVector z).1),-((D.cyclicVector z).2)) := by
  have hv := ZMod.val_lt z
  have hrval : (S.card : ZMod (2*S.card)).val=S.card :=
    ZMod.val_natCast_of_lt (by omega)
  by_cases h : z.val<S.card
  · have ha : (z+(S.card : ZMod (2*S.card))).val=z.val+S.card := by
      rw [ZMod.val_add,hrval,Nat.mod_eq_of_lt (by omega)]
    have hn : ¬(z+(S.card : ZMod (2*S.card))).val<S.card := by rw [ha]; omega
    have hn' : ¬z.val+S.card<S.card := by omega
    simp [cyclicVector,ha,h,hn']
  · have ha : (z+(S.card : ZMod (2*S.card))).val=z.val-S.card := by
      rw [ZMod.val_add_of_le (by rw [hrval]; omega),hrval]
      omega
    have hp : (z+(S.card : ZMod (2*S.card))).val<S.card := by rw [ha]; omega
    have hp' : z.val-S.card<S.card := by omega
    simp [cyclicVector,ha,h,hp',neg_neg]

private theorem next_val (z : ZMod (2*S.card)) (h : z.val+1<2*S.card) :
    (z+1).val=z.val+1 := by
  rw [ZMod.val_add]
  have hv : (1 : ZMod (2*S.card)).val=1 := by
    simpa only [Nat.cast_one] using
      (ZMod.val_natCast_of_lt (n:=2*S.card) (a:=1) (by omega))
  rw [hv,Nat.mod_eq_of_lt h]

private theorem last_next_val (hr : 2≤S.card) (z : ZMod (2*S.card))
    (h : z.val+1=2*S.card) : (z+1).val=0 := by
  rw [ZMod.val_add]
  have hv : (1 : ZMod (2*S.card)).val=1 := by
    simpa only [Nat.cast_one] using
      (ZMod.val_natCast_of_lt (n:=2*S.card) (a:=1) (by omega))
  rw [hv,h,Nat.mod_self]

/-- Appending the negative representatives yields a genuine counterclockwise
cyclic order of all 2r rays, including both half-plane transition sectors. -/
theorem cyclicVector_consecutive_positive (hr : 2≤S.card) (z : ZMod (2*S.card)) :
    0<(D.cyclicVector z).1*(D.cyclicVector (z+1)).2-
      (D.cyclicVector z).2*(D.cyclicVector (z+1)).1 := by
  have hz := ZMod.val_lt z
  by_cases hlast : z.val+1=2*S.card
  · have hv := last_next_val hr z hlast
    have hn : ¬z.val<S.card := by omega
    have h0 : (z+1).val<S.card := by rw [hv]; omega
    unfold cyclicVector
    rw [dif_neg hn,dif_pos h0]
    simp only [hv]
    have hp := D.vector_det_positive (a:=⟨0,by omega⟩)
      (b:=⟨z.val-S.card,by omega⟩) (by change 0<z.val-S.card; omega)
    nlinarith
  · have hv := next_val z (by omega)
    by_cases h : z.val<S.card
    · by_cases hnext : z.val+1<S.card
      · have hn : (z+1).val<S.card := by rw [hv]; exact hnext
        unfold cyclicVector
        rw [dif_pos h,dif_pos hn]
        simp only [hv]
        exact D.vector_det_positive (a:=⟨z.val,h⟩) (b:=⟨z.val+1,hnext⟩)
          (by change z.val<z.val+1; omega)
      · have he : z.val+1=S.card := by omega
        have hn : ¬(z+1).val<S.card := by rw [hv]; omega
        unfold cyclicVector
        rw [dif_pos h,dif_neg hn]
        simp only [hv]
        have hp := D.vector_det_positive
          (a:=⟨z.val+1-S.card,by omega⟩) (b:=⟨z.val,h⟩)
          (by change z.val+1-S.card<z.val; omega)
        nlinarith
    · have hn : ¬(z+1).val<S.card := by rw [hv]; omega
      unfold cyclicVector
      rw [dif_neg h,dif_neg hn]
      simp only [hv]
      have hp := D.vector_det_positive
        (a:=⟨z.val-S.card,by omega⟩) (b:=⟨z.val+1-S.card,by omega⟩)
        (by change z.val-S.card<z.val+1-S.card; omega)
      nlinarith

noncomputable def cyclicPoint (c : Point) (z : ZMod (2*S.card)) (scale : ℝ) : Point :=
  (c.1+scale*(D.cyclicVector z).1,c.2+scale*(D.cyclicVector z).2)

theorem cyclicPoint_on_line (c : Point)
    (hc : ∀ i∈S, affineEval (L i) c=0) (z : ZMod (2*S.card)) (scale : ℝ) :
    affineEval (L (D.cyclicRadial z)) (D.cyclicPoint c z scale)=0 := by
  have hcenter := hc (D.cyclicRadial z) (D.cyclicRadial_mem z)
  have hd := D.cyclicVector_on_line z
  dsimp [cyclicPoint,affineEval] at *
  have hm := congrArg (fun x : ℝ => scale*x) hd
  nlinarith [hm]

theorem cyclicPoint_area (c : Point) (a b : ZMod (2*S.card)) (u v : ℝ) :
    areaDet c (D.cyclicPoint c a u) (D.cyclicPoint c b v)=
      u*v*((D.cyclicVector a).1*(D.cyclicVector b).2-
        (D.cyclicVector a).2*(D.cyclicVector b).1) := by
  dsimp [cyclicPoint,areaDet]
  ring

theorem cyclicPoint_area_positive_iff (c : Point) (a b : ZMod (2*S.card))
    (u v : ℝ) (hu : 0<u) (hv : 0<v) :
    0<areaDet c (D.cyclicPoint c a u) (D.cyclicPoint c b v) ↔
      0<(D.cyclicVector a).1*(D.cyclicVector b).2-
        (D.cyclicVector a).2*(D.cyclicVector b).1 := by
  rw [D.cyclicPoint_area]
  exact mul_pos_iff_of_pos_left (mul_pos hu hv)

theorem cyclicPoint_consecutive_positive (hr : 2≤S.card) (c : Point)
    (z : ZMod (2*S.card)) (u v : ℝ) (hu : 0<u) (hv : 0<v) :
    0<areaDet c (D.cyclicPoint c z u) (D.cyclicPoint c (z+1) v) := by
  have he : areaDet c (D.cyclicPoint c z u) (D.cyclicPoint c (z+1) v)=
      u*v*((D.cyclicVector z).1*(D.cyclicVector (z+1)).2-
        (D.cyclicVector z).2*(D.cyclicVector (z+1)).1) := by
    dsimp [cyclicPoint,areaDet]
    ring
  rw [he]
  exact mul_pos (mul_pos hu hv) (D.cyclicVector_consecutive_positive hr z)

/-- Positive rescaling can choose nearest actual vertices independently on
opposite rays; antipodality survives with the explicitly positive ratio of
the two lengths. A single common distance is not required. -/
theorem cyclicPoint_antipodal (hr : 2≤S.card) (c : Point)
    (scale : ZMod (2*S.card) → ℝ) (positive : ∀ z, 0<scale z)
    (z : ZMod (2*S.card)) :
    ∃ v : ℝ, 0<v ∧
      D.cyclicPoint c (z+(S.card : ZMod (2*S.card)))
        (scale (z+(S.card : ZMod (2*S.card))))=
      (c.1-v*((D.cyclicPoint c z (scale z)).1-c.1),
       c.2-v*((D.cyclicPoint c z (scale z)).2-c.2)) := by
  refine ⟨scale (z+(S.card : ZMod (2*S.card)))/scale z,
    div_pos (positive _) (positive z),?_⟩
  simp only [cyclicPoint,D.cyclicVector_antipodal hr z]
  apply Prod.ext
  all_goals
    dsimp
    field_simp [(positive z).ne']
    ring

theorem cyclicVector_transverse (z : ZMod (2*S.card)) :
    (D.cyclicVector z).1+D.parameter*(D.cyclicVector z).2=
      if z.val<S.card then 1 else -1 := by
  unfold cyclicVector
  split_ifs with h
  · exact direction_normalized D.parameter (L (D.radial ⟨z.val,h⟩))
      (D.nonzero _)
  · have hn := direction_normalized D.parameter
      (L (D.radial ⟨z.val-S.card,by have := ZMod.val_lt z; omega⟩)) (D.nonzero _)
    change (D.vector _).1+D.parameter*(D.vector _).2=1 at hn
    dsimp
    nlinarith

theorem cyclicPoint_ne_center (c : Point) (z : ZMod (2*S.card))
    (scale : ℝ) (positive : 0<scale) : D.cyclicPoint c z scale≠c := by
  intro he
  have hp := congrArg Prod.fst he
  have hq := congrArg Prod.snd he
  have ht := D.cyclicVector_transverse z
  dsimp [cyclicPoint] at hp hq
  have hqm := congrArg (fun x : ℝ => D.parameter*x) hq
  split_ifs at ht <;>
    have hm := congrArg (fun x : ℝ => scale*x) ht <;>
    nlinarith [hm,hqm]

/-- The selected radial line and the transverse side identify each cyclic
ray uniquely. This is an actual half-plane partition, preventing duplicated
directions or multiple winding in the cyclic order. -/
theorem cyclicRadial_half_injective (a b : ZMod (2*S.card))
    (ha : (a.val<S.card)↔(b.val<S.card))
    (he : D.cyclicRadial a=D.cyclicRadial b) : a=b := by
  apply ZMod.val_injective (2*S.card)
  by_cases h : a.val<S.card
  · have hb := ha.mp h
    simp only [cyclicRadial,dif_pos h,dif_pos hb] at he
    have hh := congrArg (fun k : Fin S.card => k.val) (D.radial_injective he)
    exact hh
  · have hb : ¬b.val<S.card := fun hbb => h (ha.mpr hbb)
    simp only [cyclicRadial,dif_neg h,dif_neg hb] at he
    have hh := congrArg (fun k : Fin S.card => k.val) (D.radial_injective he)
    have hval₁ := ZMod.val_lt a
    have hval₂ := ZMod.val_lt b
    change a.val-S.card=b.val-S.card at hh
    omega

theorem cyclicPoint_injective (_hr : 2≤S.card) (c : Point)
    (hc : ∀ i∈S, affineEval (L i) c=0)
    (hL : NoParallel n L) (scale : ZMod (2*S.card) → ℝ)
    (positive : ∀ z, 0<scale z) :
    Function.Injective (fun z => D.cyclicPoint c z (scale z)) := by
  intro a b he
  change D.cyclicPoint c a (scale a)=D.cyclicPoint c b (scale b) at he
  have hnonzero := D.cyclicPoint_ne_center c a (scale a) (positive a)
  have hc₁ := hc (D.cyclicRadial a) (D.cyclicRadial_mem a)
  have hc₂ := hc (D.cyclicRadial b) (D.cyclicRadial_mem b)
  have hp₁ := D.cyclicPoint_on_line c hc a (scale a)
  have hp₂ : affineEval (L (D.cyclicRadial b)) (D.cyclicPoint c a (scale a))=0 := by
    rw [he]
    exact D.cyclicPoint_on_line c hc b (scale b)
  have hrad : D.cyclicRadial a=D.cyclicRadial b := by
    by_contra hne
    apply hnonzero
    exact two_lines_two_points (L (D.cyclicRadial a)) (L (D.cyclicRadial b))
      _ _ (noParallel_any n L hL _ _ (D.cyclicRadial a).isLt
        (D.cyclicRadial b).isLt (fun h => hne (Fin.ext h))) hp₁ hc₁ hp₂ hc₂
  apply D.cyclicRadial_half_injective a b _ hrad
  have hp := congrArg Prod.fst he
  have hq := congrArg Prod.snd he
  have hta := D.cyclicVector_transverse a
  have htb := D.cyclicVector_transverse b
  dsimp [cyclicPoint] at hp hq
  have hqm := congrArg (fun x : ℝ => D.parameter*x) hq
  by_cases ha : a.val<S.card <;> by_cases hb : b.val<S.card
  · simp [ha,hb]
  · simp only [ha,hb,ite_true,ite_false] at hta htb
    have hma := congrArg (fun x : ℝ => scale a*x) hta
    have hmb := congrArg (fun x : ℝ => scale b*x) htb
    have hpa := positive a
    have hpb := positive b
    exfalso
    nlinarith [hma,hmb,hqm]
  · simp only [ha,hb,ite_true,ite_false] at hta htb
    have hma := congrArg (fun x : ℝ => scale a*x) hta
    have hmb := congrArg (fun x : ℝ => scale b*x) htb
    have hpa := positive a
    have hpb := positive b
    exfalso
    nlinarith [hma,hmb,hqm]
  · simp [ha,hb]

end Cyclic

end OrderedDirections

/-- Apply the canonical ordering to the actual supports of any real point
in the arrangement. The caller supplies no ordering or orientation premise. -/
noncomputable def atPoint (n : ℕ) (L : ℕ → Line ℝ)
    (hL : NoParallel n L) (hn : 2≤n) (c : Point) :
    OrderedDirections n L (supports n L c) := orderedDirections n L hL hn _

#print axioms exists_transverse
#print axioms orderedDirections
#print axioms OrderedDirections.outerPoint_area_positive
#print axioms OrderedDirections.cyclicVector_antipodal
#print axioms OrderedDirections.cyclicPoint_consecutive_positive
#print axioms OrderedDirections.cyclicPoint_injective
end Kobon.UpperOpenMathRadialOrder
