import Kobon.Euclidean
import Mathlib.Data.Fintype.Card

/-! Explicit barycentric regions associated with the certificate predicate.
This module connects the polynomial certificate to geometric interiors. -/
namespace Kobon.Cells

noncomputable def weightU (p q r x : Point) : ℝ := areaDet x q r / areaDet p q r
noncomputable def weightV (p q r x : Point) : ℝ := areaDet p x r / areaDet p q r
noncomputable def weightW (p q r x : Point) : ℝ := areaDet p q x / areaDet p q r

def OpenTriangle (p q r : Point) : Set Point :=
  {x | ∃ u v w : ℝ, 0<u ∧ 0<v ∧ 0<w ∧ u+v+w=1 ∧ x=barycenter p q r u v w}

def ClosedTriangle (p q r : Point) : Set Point :=
  {x | ∃ u v w : ℝ, 0≤u ∧ 0≤v ∧ 0≤w ∧ u+v+w=1 ∧ x=barycenter p q r u v w}

theorem weights_sum (p q r x : Point) (ha : areaDet p q r≠0) :
    weightU p q r x+weightV p q r x+weightW p q r x=1 := by
  dsimp [weightU,weightV,weightW]
  field_simp
  dsimp [areaDet]
  ring

theorem weights_reconstruct (p q r x : Point) (ha : areaDet p q r≠0) :
    x=barycenter p q r (weightU p q r x) (weightV p q r x) (weightW p q r x) := by
  apply Prod.ext <;> dsimp [barycenter,weightU,weightV,weightW]
  all_goals field_simp
  all_goals dsimp [areaDet]; ring

theorem weights_barycenter (p q r : Point) (ha : areaDet p q r≠0)
    (u v w : ℝ) (hs : u+v+w=1) :
    weightU p q r (barycenter p q r u v w)=u ∧
    weightV p q r (barycenter p q r u v w)=v ∧
    weightW p q r (barycenter p q r u v w)=w := by
  have hw : w=1-u-v := by linarith
  subst w
  dsimp [weightU,weightV,weightW,barycenter]
  constructor
  · apply (div_eq_iff ha).mpr
    dsimp [areaDet]; ring
  constructor <;> apply (div_eq_iff ha).mpr <;> dsimp [areaDet] <;> ring

theorem open_iff_weights (p q r x : Point) (ha : areaDet p q r≠0) :
    x∈OpenTriangle p q r ↔
      0<weightU p q r x ∧ 0<weightV p q r x ∧ 0<weightW p q r x := by
  constructor
  · rintro ⟨u,v,w,hu,hv,hw,hs,rfl⟩
    rcases weights_barycenter p q r ha u v w hs with ⟨e1,e2,e3⟩
    simpa only [e1,e2,e3] using And.intro hu (And.intro hv hw)
  · rintro ⟨hu,hv,hw⟩
    exact ⟨_,_,_,hu,hv,hw,weights_sum p q r x ha,weights_reconstruct p q r x ha⟩

theorem closed_iff_weights (p q r x : Point) (ha : areaDet p q r≠0) :
    x∈ClosedTriangle p q r ↔
      0≤weightU p q r x ∧ 0≤weightV p q r x ∧ 0≤weightW p q r x := by
  constructor
  · rintro ⟨u,v,w,hu,hv,hw,hs,rfl⟩
    rcases weights_barycenter p q r ha u v w hs with ⟨e1,e2,e3⟩
    simpa only [e1,e2,e3] using And.intro hu (And.intro hv hw)
  · rintro ⟨hu,hv,hw⟩
    exact ⟨_,_,_,hu,hv,hw,weights_sum p q r x ha,weights_reconstruct p q r x ha⟩

theorem weights_affineEval (p q r x : Point) (ha : areaDet p q r≠0) (l : Line ℝ) :
    affineEval l x=weightU p q r x*affineEval l p+
      weightV p q r x*affineEval l q+weightW p q r x*affineEval l r := by
  conv_lhs => rw [weights_reconstruct p q r x ha]
  exact affineEval_barycenter l p q r _ _ _ (weights_sum p q r x ha)

theorem support_weight (p q r x : Point) (ha : areaDet p q r≠0) (l : Line ℝ)
    (hq : affineEval l q=0) (hr : affineEval l r=0) :
    affineEval l x=weightU p q r x*affineEval l p := by
  simpa [hq,hr] using weights_affineEval p q r x ha l

theorem nondegenerate_pair_ne (p q r : Point) (ha : areaDet p q r≠0) : p≠q := by
  rintro rfl
  simp [areaDet] at ha

theorem two_lines_two_points (l m : Line ℝ) (p q : Point) (h : det l m≠0)
    (hlp : affineEval l p=0) (hlq : affineEval l q=0)
    (hmp : affineEval m p=0) (hmq : affineEval m q=0) : p=q := by
  have hx : det l m*(p.1-q.1)=0 := by
    calc
      det l m*(p.1-q.1)=(affineEval l p-affineEval l q)*m.b-
          (affineEval m p-affineEval m q)*l.b := by dsimp [det,affineEval]; ring
      _=0 := by rw [hlp,hlq,hmp,hmq]; ring
  have hy : det l m*(p.2-q.2)=0 := by
    calc
      det l m*(p.2-q.2)=(affineEval m p-affineEval m q)*l.a-
          (affineEval l p-affineEval l q)*m.a := by dsimp [det,affineEval]; ring
      _=0 := by rw [hlp,hlq,hmp,hmq]; ring
  apply Prod.ext
  · exact sub_eq_zero.mp ((mul_eq_zero.mp hx).resolve_left h)
  · exact sub_eq_zero.mp ((mul_eq_zero.mp hy).resolve_left h)

structure TriangleGeometry where
  p : Point
  q : Point
  r : Point
  A : Line ℝ
  B : Line ℝ
  C : Line ℝ
  nondegenerate : areaDet p q r≠0
  Aq : affineEval A q=0
  Ar : affineEval A r=0
  Bp : affineEval B p=0
  Br : affineEval B r=0
  Cp : affineEval C p=0
  Cq : affineEval C q=0
  Ap : affineEval A p≠0
  Bq : affineEval B q≠0
  Cr : affineEval C r≠0

namespace TriangleGeometry

def interior (t : TriangleGeometry) : Set Point := OpenTriangle t.p t.q t.r
def closed (t : TriangleGeometry) : Set Point := ClosedTriangle t.p t.q t.r

theorem eval_A (t : TriangleGeometry) (x : Point) :
    affineEval t.A x=weightU t.p t.q t.r x*affineEval t.A t.p :=
  support_weight _ _ _ x t.nondegenerate t.A t.Aq t.Ar

theorem eval_B (t : TriangleGeometry) (x : Point) :
    affineEval t.B x=weightV t.p t.q t.r x*affineEval t.B t.q := by
  simpa [t.Bp,t.Br] using weights_affineEval t.p t.q t.r x t.nondegenerate t.B

theorem eval_C (t : TriangleGeometry) (x : Point) :
    affineEval t.C x=weightW t.p t.q t.r x*affineEval t.C t.r := by
  simpa [t.Cp,t.Cq] using weights_affineEval t.p t.q t.r x t.nondegenerate t.C

theorem open_weights (t : TriangleGeometry) (x : Point) :
    x∈t.interior ↔ 0<weightU t.p t.q t.r x ∧
      0<weightV t.p t.q t.r x ∧ 0<weightW t.p t.q t.r x :=
  open_iff_weights _ _ _ x t.nondegenerate

theorem closed_weights (t : TriangleGeometry) (x : Point) :
    x∈t.closed ↔ 0≤weightU t.p t.q t.r x ∧
      0≤weightV t.p t.q t.r x ∧ 0≤weightW t.p t.q t.r x :=
  closed_iff_weights _ _ _ x t.nondegenerate

theorem product_sign (a u v : ℝ) (ha : a≠0) (hu : 0<u) :
    0≤(u*a)*(v*a) ↔ 0≤v := by
  have hp : 0<u*a^2 := mul_pos hu (sq_pos_of_ne_zero ha)
  have he : (u*a)*(v*a)=v*(u*a^2) := by ring
  rw [he]
  exact mul_nonneg_iff_of_pos_right hp

theorem closed_iff_supports (t : TriangleGeometry) (z x : Point) (hz : z∈t.interior) :
    x∈t.closed ↔
      0≤affineEval t.A z*affineEval t.A x ∧
      0≤affineEval t.B z*affineEval t.B x ∧
      0≤affineEval t.C z*affineEval t.C x := by
  rcases (t.open_weights z).mp hz with ⟨hu,hv,hw⟩
  rw [t.closed_weights x,t.eval_A z,t.eval_A x,t.eval_B z,t.eval_B x,t.eval_C z,t.eval_C x]
  simp only [product_sign _ _ _ t.Ap hu,product_sign _ _ _ t.Bq hv,product_sign _ _ _ t.Cr hw]

theorem closed_nonzero_is_open (t : TriangleGeometry) (x : Point)
    (hx : x∈t.closed) (hA : affineEval t.A x≠0)
    (hB : affineEval t.B x≠0) (hC : affineEval t.C x≠0) : x∈t.interior := by
  rcases (t.closed_weights x).mp hx with ⟨hu,hv,hw⟩
  apply (t.open_weights x).mpr
  rw [t.eval_A x] at hA
  rw [t.eval_B x] at hB
  rw [t.eval_C x] at hC
  exact ⟨lt_of_le_of_ne hu (fun h => hA (by rw [← h,zero_mul])),
    lt_of_le_of_ne hv (fun h => hB (by rw [← h,zero_mul])),
    lt_of_le_of_ne hw (fun h => hC (by rw [← h,zero_mul]))⟩

end TriangleGeometry

def WeakSide (l : Line ℝ) (p q r : Point) : Prop :=
  (0≤affineEval l p ∧ 0≤affineEval l q ∧ 0≤affineEval l r) ∨
  (affineEval l p≤0 ∧ affineEval l q≤0 ∧ affineEval l r≤0)

theorem weakSide_products (l : Line ℝ) (p q r z : Point)
    (hs : WeakSide l p q r) (hz : z∈OpenTriangle p q r) :
    0≤affineEval l z*affineEval l p ∧
    0≤affineEval l z*affineEval l q ∧
    0≤affineEval l z*affineEval l r := by
  rcases hz with ⟨u,v,w,hu,hv,hw,hsum,rfl⟩
  rw [affineEval_barycenter l p q r u v w hsum]
  rcases hs with ⟨hp,hq,hr⟩ | ⟨hp,hq,hr⟩
  · have h : 0≤u*affineEval l p+v*affineEval l q+w*affineEval l r :=
      add_nonneg (add_nonneg (mul_nonneg hu.le hp) (mul_nonneg hv.le hq)) (mul_nonneg hw.le hr)
    exact ⟨mul_nonneg h hp,mul_nonneg h hq,mul_nonneg h hr⟩
  · have h : u*affineEval l p+v*affineEval l q+w*affineEval l r≤0 :=
      add_nonpos (add_nonpos (mul_nonpos_of_nonneg_of_nonpos hu.le hp)
        (mul_nonpos_of_nonneg_of_nonpos hv.le hq)) (mul_nonpos_of_nonneg_of_nonpos hw.le hr)
    exact ⟨mul_nonneg_of_nonpos_of_nonpos h hp,
      mul_nonneg_of_nonpos_of_nonpos h hq,mul_nonneg_of_nonpos_of_nonpos h hr⟩

theorem vertices_contained (t s : TriangleGeometry) (z : Point)
    (htz : z∈t.interior) (hsz : z∈s.interior)
    (hA : WeakSide s.A t.p t.q t.r)
    (hB : WeakSide s.B t.p t.q t.r)
    (hC : WeakSide s.C t.p t.q t.r) :
    t.p∈s.closed ∧ t.q∈s.closed ∧ t.r∈s.closed := by
  have a := weakSide_products s.A t.p t.q t.r z hA htz
  have b := weakSide_products s.B t.p t.q t.r z hB htz
  have c := weakSide_products s.C t.p t.q t.r z hC htz
  exact ⟨(s.closed_iff_supports z t.p hsz).mpr ⟨a.1,b.1,c.1⟩,
    (s.closed_iff_supports z t.q hsz).mpr ⟨a.2.1,b.2.1,c.2.1⟩,
    (s.closed_iff_supports z t.r hsz).mpr ⟨a.2.2,b.2.2,c.2.2⟩⟩

noncomputable def segmentPoint (p q : Point) (u : ℝ) : Point :=
  ((1-u)*p.1+u*q.1,(1-u)*p.2+u*q.2)

theorem affineEval_segment (l : Line ℝ) (p q : Point) (u : ℝ) :
    affineEval l (segmentPoint p q u)=(1-u)*affineEval l p+u*affineEval l q := by
  dsimp [segmentPoint,affineEval]
  ring

theorem segment_injective (p q : Point) (hpq : p≠q) :
    Function.Injective (segmentPoint p q) := by
  intro u v he
  by_contra hne
  have hd : u-v≠0 := sub_ne_zero.mpr hne
  have hx := congrArg Prod.fst he
  have hy := congrArg Prod.snd he
  have h1 : (u-v)*(q.1-p.1)=0 := by dsimp [segmentPoint] at hx; nlinarith
  have h2 : (u-v)*(q.2-p.2)=0 := by dsimp [segmentPoint] at hy; nlinarith
  apply hpq
  apply Prod.ext
  · exact (sub_eq_zero.mp ((mul_eq_zero.mp h1).resolve_left hd)).symm
  · exact (sub_eq_zero.mp ((mul_eq_zero.mp h2).resolve_left hd)).symm

theorem segment_closed (t : TriangleGeometry) (p q : Point) (hp : p∈t.closed)
    (hq : q∈t.closed) (u : ℝ) (hu : 0≤u) (hu1 : u≤1) :
    segmentPoint p q u∈t.closed := by
  rcases (t.closed_weights p).mp hp with ⟨hp1,hp2,hp3⟩
  rcases (t.closed_weights q).mp hq with ⟨hq1,hq2,hq3⟩
  have h1 : weightU t.p t.q t.r (segmentPoint p q u)=
      (1-u)*weightU t.p t.q t.r p+u*weightU t.p t.q t.r q := by
    dsimp [weightU,areaDet,segmentPoint]; ring
  have h2 : weightV t.p t.q t.r (segmentPoint p q u)=
      (1-u)*weightV t.p t.q t.r p+u*weightV t.p t.q t.r q := by
    dsimp [weightV,areaDet,segmentPoint]; ring
  have h3 : weightW t.p t.q t.r (segmentPoint p q u)=
      (1-u)*weightW t.p t.q t.r p+u*weightW t.p t.q t.r q := by
    dsimp [weightW,areaDet,segmentPoint]; ring
  apply (t.closed_weights _).mpr
  rw [h1,h2,h3]
  exact ⟨add_nonneg (mul_nonneg (sub_nonneg.mpr hu1) hp1) (mul_nonneg hu hq1),
    add_nonneg (mul_nonneg (sub_nonneg.mpr hu1) hp2) (mul_nonneg hu hq2),
    add_nonneg (mul_nonneg (sub_nonneg.mpr hu1) hp3) (mul_nonneg hu hq3)⟩

theorem side_parallel_to_support (t : TriangleGeometry) (l : Line ℝ) (p q : Point)
    (hpq : p≠q) (hp : p∈t.closed) (hq : q∈t.closed)
    (hlp : affineEval l p=0) (hlq : affineEval l q=0)
    (huncut : ∀ x∈t.interior, affineEval l x≠0) :
    det l t.A=0 ∨ det l t.B=0 ∨ det l t.C=0 := by
  classical
  by_contra h
  have hA : det l t.A≠0 := by tauto
  have hB : det l t.B≠0 := by tauto
  have hC : det l t.C≠0 := by tauto
  let point : Fin 4 → Point := fun i => segmentPoint p q (((i.val:ℝ)+1)/5)
  have hinj : Function.Injective point := by
    intro i j he
    have hv := segment_injective p q hpq he
    have heq : (i.val:ℝ)=(j.val:ℝ) := by linarith
    exact Fin.ext (by exact_mod_cast heq)
  have hpoint : ∀ i, point i∈t.closed := by
    intro i
    apply segment_closed t p q hp hq
    · positivity
    · have hv : (i.val:ℝ)<4 := by exact_mod_cast i.isLt
      linarith
  have hline : ∀ i, affineEval l (point i)=0 := by
    intro i
    dsimp [point]
    rw [affineEval_segment,hlp,hlq]
    ring
  let supports : Fin 3 → Line ℝ := fun i => if i=0 then t.A else if i=1 then t.B else t.C
  have hex : ∀ i : Fin 4, ∃ j : Fin 3, affineEval (supports j) (point i)=0 := by
    intro i
    by_cases h0 : affineEval t.A (point i)=0
    · exact ⟨0,by simpa [supports] using h0⟩
    by_cases h1 : affineEval t.B (point i)=0
    · exact ⟨1,by simpa [supports] using h1⟩
    by_cases h2 : affineEval t.C (point i)=0
    · exact ⟨2,by simpa [supports] using h2⟩
    exact False.elim (huncut _ (t.closed_nonzero_is_open _ (hpoint i) h0 h1 h2) (hline i))
  choose f hf using hex
  have hf_inj : Function.Injective f := by
    intro i j he
    apply hinj
    have hn : det l (supports (f i))≠0 := by
      dsimp [supports]
      split
      · exact hA
      split
      · exact hB
      · exact hC
    apply two_lines_two_points l (supports (f i)) _ _ hn (hline i) (hline j) (hf i)
    rw [he]
    exact hf j
  have hc := Fintype.card_le_of_injective f hf_inj
  norm_num at hc

theorem noParallel_any (n : ℕ) (L : ℕ → Line ℝ) (hp : NoParallel n L)
    (i j : ℕ) (hi : i<n) (hj : j<n) (hne : i≠j) : det (L i) (L j)≠0 := by
  rcases lt_or_gt_of_ne hne with h | h
  · exact hp ⟨i,hi⟩ ⟨j,hj⟩ h
  · have hd := hp ⟨j,hj⟩ ⟨i,hi⟩ h
    have he : det (L i) (L j)=-det (L j) (L i) := by dsimp [det]; ring
    rw [he]
    exact neg_ne_zero.mpr hd

theorem line_valid (n : ℕ) (L : ℕ → Line ℝ) (hp : NoParallel n L) (hn : 2≤n)
    (i : Fin n) : (L i).a≠0 ∨ (L i).b≠0 := by
  by_contra h
  have ha : (L i).a=0 := by tauto
  have hb : (L i).b=0 := by tauto
  by_cases hi : i.val=0
  · have hd := noParallel_any n L hp i.val 1 i.isLt (by omega) (by omega)
    simp [det,ha,hb] at hd
  · have hd := noParallel_any n L hp i.val 0 i.isLt (by omega) hi
    simp [det,ha,hb] at hd

noncomputable def ofPredicate (n : ℕ) (L : ℕ → Line ℝ) (t : Triple)
    (hp : NoParallel n L) (ht : TrianglePredicate n L t) : TriangleGeometry := by
  have hij := ht.1
  have hjk := ht.2.1
  have hkn := ht.2.2.1
  have hi : t.i<n := by omega
  have hj : t.j<n := by omega
  have dij := hp ⟨t.i,hi⟩ ⟨t.j,hj⟩ hij
  have dik := hp ⟨t.i,hi⟩ ⟨t.k,hkn⟩ (by change t.i<t.k; omega)
  have djk := hp ⟨t.j,hj⟩ ⟨t.k,hkn⟩ hjk
  let p := intersection (L t.i) (L t.j)
  let q := intersection (L t.i) (L t.k)
  let r := intersection (L t.j) (L t.k)
  have ha : areaDet p q r≠0 := supporting_triangle_nondegenerate _ _ _ dij dik djk ht.2.2.2.1
  have cp : affineEval (L t.i) p=0 := intersection_on_left _ _ dij
  have cq : affineEval (L t.i) q=0 := intersection_on_left _ _ dik
  have bp : affineEval (L t.j) p=0 := intersection_on_right _ _ dij
  have br : affineEval (L t.j) r=0 := intersection_on_left _ _ djk
  have aq : affineEval (L t.k) q=0 := intersection_on_right _ _ dik
  have ar : affineEval (L t.k) r=0 := intersection_on_right _ _ djk
  refine ⟨p,q,r,L t.k,L t.j,L t.i,ha,aq,ar,bp,br,cp,cq,?_,?_,?_⟩
  · rw [eval_intersection _ _ _ dij]
    exact div_ne_zero ht.2.2.2.1 dij
  · intro hzero
    have h := three_zeros_force_zero_normal (L t.j) p q r ha bp hzero br
    have hv := line_valid n L hp (by omega) ⟨t.j,hj⟩
    exact hv.elim (fun hn => hn h.1) (fun hn => hn h.2)
  · intro hzero
    have h := three_zeros_force_zero_normal (L t.i) p q r ha cp cq hzero
    have hv := line_valid n L hp (by omega) ⟨t.i,hi⟩
    exact hv.elim (fun hn => hn h.1) (fun hn => hn h.2)

theorem weakSide_of_predicate (n : ℕ) (L : ℕ → Line ℝ) (t : Triple)
    (hp : NoParallel n L) (ht : TrianglePredicate n L t) (r : Fin n) :
    WeakSide (L r) (ofPredicate n L t hp ht).p (ofPredicate n L t hp ht).q
      (ofPredicate n L t hp ht).r := by
  have hij := ht.1
  have hjk := ht.2.1
  have hkn := ht.2.2.1
  have hi : t.i<n := by omega
  have hj : t.j<n := by omega
  have dij := hp ⟨t.i,hi⟩ ⟨t.j,hj⟩ hij
  have dik := hp ⟨t.i,hi⟩ ⟨t.k,hkn⟩ (by change t.i<t.k; omega)
  have djk := hp ⟨t.j,hj⟩ ⟨t.k,hkn⟩ hjk
  change WeakSide (L r) (intersection (L t.i) (L t.j))
    (intersection (L t.i) (L t.k)) (intersection (L t.j) (L t.k))
  rcases ht.2.2.2.2 r with ⟨h1,h2,h3⟩ | ⟨h1,h2,h3⟩
  · exact Or.inl ⟨(oriented_nonneg_iff _ _ _ dij).mp h1,
      (oriented_nonneg_iff _ _ _ dik).mp h2,(oriented_nonneg_iff _ _ _ djk).mp h3⟩
  · exact Or.inr ⟨(oriented_nonpos_iff _ _ _ dij).mp h1,
      (oriented_nonpos_iff _ _ _ dik).mp h2,(oriented_nonpos_iff _ _ _ djk).mp h3⟩

theorem interior_uncut (n : ℕ) (L : ℕ → Line ℝ) (t : Triple)
    (hp : NoParallel n L) (ht : TrianglePredicate n L t) (r : Fin n) :
    ∀ x∈(ofPredicate n L t hp ht).interior, affineEval (L r) x≠0 := by
  intro x hx
  have hn : 2≤n := by have := ht.1; have := ht.2.1; have := ht.2.2.1; omega
  rcases hx with ⟨u,v,w,hu,hv,hw,hs,rfl⟩
  exact triangle_interior_uncut (L r) _ _ _ (line_valid n L hp hn r)
    (ofPredicate n L t hp ht).nondegenerate u v w hu hv hw hs
    (weakSide_of_predicate n L t hp ht r)

theorem side_index_mem (n : ℕ) (L : ℕ → Line ℝ) (s : Triple)
    (hp : NoParallel n L) (hs : TrianglePredicate n L s)
    (a : ℕ) (ha : a<n) (p q : Point) (hpq : p≠q)
    (hpc : p∈(ofPredicate n L s hp hs).closed)
    (hqc : q∈(ofPredicate n L s hp hs).closed)
    (hlp : affineEval (L a) p=0) (hlq : affineEval (L a) q=0) :
    a=s.i ∨ a=s.j ∨ a=s.k := by
  have hh := side_parallel_to_support (ofPredicate n L s hp hs) (L a) p q hpq hpc hqc hlp hlq
    (interior_uncut n L s hp hs ⟨a,ha⟩)
  change det (L a) (L s.k)=0 ∨ det (L a) (L s.j)=0 ∨ det (L a) (L s.i)=0 at hh
  have hi : s.i<n := by have := hs.1; have := hs.2.1; have := hs.2.2.1; omega
  have hj : s.j<n := by have := hs.2.1; have := hs.2.2.1; omega
  have hk := hs.2.2.1
  rcases hh with hh | hh | hh
  · right; right
    by_contra hne
    exact noParallel_any n L hp a s.k ha hk hne hh
  · right; left
    by_contra hne
    exact noParallel_any n L hp a s.j ha hj hne hh
  · left
    by_contra hne
    exact noParallel_any n L hp a s.i ha hi hne hh

/-- Distinct supporting triples cannot describe overlapping open triangles. -/
theorem overlap_forces_same_triple (n : ℕ) (L : ℕ → Line ℝ) (t s : Triple)
    (hp : NoParallel n L) (ht : TrianglePredicate n L t) (hs : TrianglePredicate n L s)
    (z : Point) (htz : z∈(ofPredicate n L t hp ht).interior)
    (hsz : z∈(ofPredicate n L s hp hs).interior) : t=s := by
  let T := ofPredicate n L t hp ht
  let S := ofPredicate n L s hp hs
  have hin : ∀ a, a<n → WeakSide (L a) T.p T.q T.r := by
    intro a ha
    exact weakSide_of_predicate n L t hp ht ⟨a,ha⟩
  have tsi := ht.1
  have tsj := ht.2.1
  have tsk := ht.2.2.1
  have ssi := hs.1
  have ssj := hs.2.1
  have ssk := hs.2.2.1
  have hA : WeakSide S.A T.p T.q T.r := hin s.k ssk
  have hB : WeakSide S.B T.p T.q T.r := hin s.j (by omega)
  have hC : WeakSide S.C T.p T.q T.r := hin s.i (by omega)
  rcases vertices_contained T S z htz hsz hA hB hC with ⟨hpS,hqS,hrS⟩
  have hpq : T.p≠T.q := nondegenerate_pair_ne _ _ _ T.nondegenerate
  have hpr : T.p≠T.r := by
    intro he
    have hh := T.nondegenerate
    rw [← he] at hh
    simp [areaDet] at hh
  have hqr : T.q≠T.r := by
    intro he
    have hh := T.nondegenerate
    rw [← he] at hh
    apply hh
    dsimp [areaDet]
    ring
  have hi : t.i=s.i ∨ t.i=s.j ∨ t.i=s.k :=
    side_index_mem n L s hp hs t.i (by omega) T.p T.q hpq hpS hqS T.Cp T.Cq
  have hj : t.j=s.i ∨ t.j=s.j ∨ t.j=s.k :=
    side_index_mem n L s hp hs t.j (by omega) T.p T.r hpr hpS hrS T.Bp T.Br
  have hk : t.k=s.i ∨ t.k=s.j ∨ t.k=s.k :=
    side_index_mem n L s hp hs t.k tsk T.q T.r hqr hqS hrS T.Aq T.Ar
  have e1 : t.i=s.i := by omega
  have e2 : t.j=s.j := by omega
  have e3 : t.k=s.k := by omega
  cases t
  cases s
  simp_all

theorem distinct_interiors_disjoint (n : ℕ) (L : ℕ → Line ℝ) (t s : Triple)
    (hp : NoParallel n L) (ht : TrianglePredicate n L t) (hs : TrianglePredicate n L s)
    (hne : t≠s) :
    Disjoint (ofPredicate n L t hp ht).interior (ofPredicate n L s hp hs).interior := by
  apply Set.disjoint_left.mpr
  intro z htz hsz
  exact hne (overlap_forces_same_triple n L t s hp ht hs z htz hsz)

theorem interior_nonempty (t : TriangleGeometry) : t.interior.Nonempty := by
  refine ⟨barycenter t.p t.q t.r (1/3) (1/3) (1/3),1/3,1/3,1/3,?_,?_,?_,?_,rfl⟩
  all_goals norm_num

theorem weakSide_product_interior (l : Line ℝ) (p q r z x : Point)
    (hs : WeakSide l p q r) (hz : z∈OpenTriangle p q r) (hx : x∈OpenTriangle p q r)
    (hzn : affineEval l z≠0) (hxn : affineEval l x≠0) :
    0<affineEval l z*affineEval l x := by
  have hh := weakSide_products l p q r z hs hz
  rcases hx with ⟨u,v,w,hu,hv,hw,hsum,rfl⟩
  have hprod : 0≤affineEval l z*affineEval l (barycenter p q r u v w) := by
    calc
      0≤u*(affineEval l z*affineEval l p)+v*(affineEval l z*affineEval l q)+
          w*(affineEval l z*affineEval l r) :=
        add_nonneg (add_nonneg (mul_nonneg hu.le hh.1) (mul_nonneg hv.le hh.2.1))
          (mul_nonneg hw.le hh.2.2)
      _=affineEval l z*affineEval l (barycenter p q r u v w) := by
        rw [affineEval_barycenter l p q r u v w hsum]
        ring
  exact lt_of_le_of_ne hprod (mul_ne_zero hzn hxn).symm

def signCell (n : ℕ) (L : ℕ → Line ℝ) (z : Point) : Set Point :=
  {x | ∀ r : Fin n, 0<affineEval (L r) z*affineEval (L r) x}

/-- Every certified open triangle is exactly one strict sign cell of the full arrangement. -/
theorem interior_eq_signCell (n : ℕ) (L : ℕ → Line ℝ) (t : Triple)
    (hp : NoParallel n L) (ht : TrianglePredicate n L t)
    (z : Point) (hz : z∈(ofPredicate n L t hp ht).interior) :
    (ofPredicate n L t hp ht).interior=signCell n L z := by
  let T := ofPredicate n L t hp ht
  apply Set.ext
  intro x
  constructor
  · intro hx r
    exact weakSide_product_interior (L r) T.p T.q T.r z x
      (weakSide_of_predicate n L t hp ht r) hz hx
      (interior_uncut n L t hp ht r z hz) (interior_uncut n L t hp ht r x hx)
  · intro hx
    have hi : t.i<n := by have := ht.1; have := ht.2.1; have := ht.2.2.1; omega
    have hj : t.j<n := by have := ht.2.1; have := ht.2.2.1; omega
    have hk := ht.2.2.1
    have hA : 0<affineEval T.A z*affineEval T.A x := hx ⟨t.k,hk⟩
    have hB : 0<affineEval T.B z*affineEval T.B x := hx ⟨t.j,hj⟩
    have hC : 0<affineEval T.C z*affineEval T.C x := hx ⟨t.i,hi⟩
    apply T.closed_nonzero_is_open x ((T.closed_iff_supports z x hz).mpr ⟨hA.le,hB.le,hC.le⟩)
    · intro he; rw [he,mul_zero] at hA; exact (lt_irrefl 0) hA
    · intro he; rw [he,mul_zero] at hB; exact (lt_irrefl 0) hB
    · intro he; rw [he,mul_zero] at hC; exact (lt_irrefl 0) hC

#print axioms overlap_forces_same_triple
#print axioms distinct_interiors_disjoint
#print axioms interior_eq_signCell
end Kobon.Cells
