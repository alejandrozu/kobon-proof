import Kobon.UpperEdgeCapacity
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Prod

/-!
# Exact finite edge incidence for actual disjoint triangles

Unordered pairs of real points represent sides. Each triangle has three
distinct sides. The geometric capacity-two theorem then proves the exact
identity `3 * number_of_triangles = used_sides + shared_sides`.

No global edge count or side-capacity assumption is present. Application to
an arrangement's total elementary-edge count is a separate next step.
-/
namespace Kobon.UpperTriangleIncidence
open Cells Finset
open scoped BigOperators

noncomputable def cycle (t : TriangleGeometry) : TriangleGeometry where
  p := t.q
  q := t.r
  r := t.p
  A := t.B
  B := t.C
  C := t.A
  nondegenerate := by
    have he : areaDet t.q t.r t.p=areaDet t.p t.q t.r := by dsimp [areaDet]; ring
    rw [he]
    exact t.nondegenerate
  Aq := t.Br
  Ar := t.Bp
  Bp := t.Cq
  Br := t.Cp
  Cp := t.Aq
  Cq := t.Ar
  Ap := t.Bq
  Bq := t.Cr
  Cr := t.Ap

noncomputable def swap (t : TriangleGeometry) : TriangleGeometry where
  p := t.q
  q := t.p
  r := t.r
  A := t.B
  B := t.A
  C := t.C
  nondegenerate := by
    have he : areaDet t.q t.p t.r= -areaDet t.p t.q t.r := by dsimp [areaDet]; ring
    rw [he]
    exact neg_ne_zero.mpr t.nondegenerate
  Aq := t.Bp
  Ar := t.Br
  Bp := t.Aq
  Br := t.Ar
  Cp := t.Cq
  Cq := t.Cp
  Ap := t.Bq
  Bq := t.Ap
  Cr := t.Cr

@[simp] theorem cycle_interior (t : TriangleGeometry) : (cycle t).interior=t.interior := by
  ext x
  constructor
  · rintro ⟨u,v,w,hu,hv,hw,hs,hx⟩
    refine ⟨w,u,v,hw,hu,hv,by linarith,?_⟩
    rw [hx]
    apply Prod.ext <;> dsimp [cycle,barycenter] <;> ring
  · rintro ⟨u,v,w,hu,hv,hw,hs,hx⟩
    refine ⟨v,w,u,hv,hw,hu,by linarith,?_⟩
    rw [hx]
    apply Prod.ext <;> dsimp [cycle,barycenter] <;> ring

@[simp] theorem swap_interior (t : TriangleGeometry) : (swap t).interior=t.interior := by
  ext x
  constructor
  · rintro ⟨u,v,w,hu,hv,hw,hs,hx⟩
    refine ⟨v,u,w,hv,hu,hw,by linarith,?_⟩
    rw [hx]
    apply Prod.ext <;> dsimp [swap,barycenter] <;> ring
  · rintro ⟨u,v,w,hu,hv,hw,hs,hx⟩
    refine ⟨v,u,w,hv,hu,hw,by linarith,?_⟩
    rw [hx]
    apply Prod.ext <;> dsimp [swap,barycenter] <;> ring

noncomputable def sideTriangle (t : TriangleGeometry) (i : Fin 3) : TriangleGeometry :=
  if i=0 then t else if i=1 then cycle t else cycle (cycle t)

@[simp] theorem sideTriangle_interior (t : TriangleGeometry) (i : Fin 3) :
    (sideTriangle t i).interior=t.interior := by
  fin_cases i <;> simp [sideTriangle]

abbrev Edge := Finset Point

noncomputable def edge (t : TriangleGeometry) (i : Fin 3) : Edge := by
  classical
  exact {(sideTriangle t i).p,(sideTriangle t i).q}

theorem edge_card (t : TriangleGeometry) (i : Fin 3) : (edge t i).card=2 := by
  classical
  exact card_pair (nondegenerate_pair_ne _ _ _ (sideTriangle t i).nondegenerate)

theorem edge_injective (t : TriangleGeometry) : Function.Injective (edge t) := by
  classical
  have hpq : t.p≠t.q := nondegenerate_pair_ne _ _ _ t.nondegenerate
  have hpr : t.p≠t.r := by intro h; exact t.Ap (h ▸ t.Ar)
  have hqr : t.q≠t.r := by intro h; exact t.Bq (h ▸ t.Br)
  intro i j he
  fin_cases i <;> fin_cases j
  all_goals try rfl
  all_goals
    simp only [edge,sideTriangle,cycle,Fin.reduceFinMk,ite_true,ite_false] at he
    have h₁ := congrArg (fun e : Edge => t.p∈e) he
    have h₂ := congrArg (fun e : Edge => t.q∈e) he
    simp [hpq,hpr,hqr,Ne.symm hpq,Ne.symm hpr,Ne.symm hqr] at h₁ h₂

/-- An unordered side can always be oriented to prescribed distinct endpoints
without changing the triangle's actual interior. -/
theorem align_edge (t : TriangleGeometry) (i : Fin 3) (p q : Point) (_hpq : p≠q)
    (he : edge t i={p,q}) :
    ∃ s : TriangleGeometry, s.p=p ∧ s.q=q ∧ s.interior=t.interior := by
  classical
  let s := sideTriangle t i
  have hsp : s.p=p ∨ s.p=q := by
    have h : s.p∈edge t i := by simp [edge,s]
    simpa only [he,mem_insert,mem_singleton] using h
  have hsq : s.q=p ∨ s.q=q := by
    have h : s.q∈edge t i := by simp [edge,s]
    simpa only [he,mem_insert,mem_singleton] using h
  have hne := nondegenerate_pair_ne s.p s.q s.r s.nondegenerate
  rcases hsp with hsp|hsp <;> rcases hsq with hsq|hsq
  · exact False.elim (hne (hsp.trans hsq.symm))
  · exact ⟨s,hsp,hsq,sideTriangle_interior t i⟩
  · exact ⟨swap s,hsq,hsp,by simp [s]⟩
  · exact False.elim (hne (hsp.trans hsq.symm))

section Counting
variable {α : Type*} [Fintype α] (t : α → TriangleGeometry)

noncomputable def sideMap (a : α × Fin 3) : Edge := edge (t a.1) a.2

noncomputable def usedEdges : Finset Edge := by
  classical
  exact univ.image (sideMap t)

noncomputable def degree (e : Edge) : ℕ := by
  classical
  exact (univ.filter (fun a : α × Fin 3 => sideMap t a=e)).card

noncomputable def sharedEdges : Finset Edge := by
  classical
  exact (usedEdges t).filter (fun e => degree t e=2)

theorem degree_le_two
    (hd : Pairwise (fun a b => Disjoint (t a).interior (t b).interior))
    (e : Edge) : degree t e≤2 := by
  classical
  let β := {a : α × Fin 3 // sideMap t a=e}
  have hcard : degree t e=Fintype.card β := by
    simp only [degree,β,Fintype.card_subtype]
  rw [hcard]
  by_cases hb : Nonempty β
  · obtain ⟨a⟩ := hb
    let p := (sideTriangle (t a.val.1) a.val.2).p
    let q := (sideTriangle (t a.val.1) a.val.2).q
    have hpq : p≠q := nondegenerate_pair_ne _ _ _ (sideTriangle (t a.val.1) a.val.2).nondegenerate
    have hex (b : β) : ∃ s : TriangleGeometry, s.p=p ∧ s.q=q ∧ s.interior=(t b.val.1).interior := by
      apply align_edge (t b.val.1) b.val.2 p q hpq
      exact b.property.trans a.property.symm
    choose f hf using hex
    apply UpperEdgeCapacity.at_most_two p q f (fun b => (hf b).1) (fun b => (hf b).2.1)
    intro b c hbc
    rw [(hf b).2.2,(hf c).2.2]
    apply hd
    intro h
    have hside : b.val.2=c.val.2 := by
      apply edge_injective (t c.val.1)
      have hh := b.property.trans c.property.symm
      simpa only [sideMap,h] using hh
    exact hbc (Subtype.ext (Prod.ext h hside))
  · haveI : IsEmpty β := not_nonempty_iff.mp hb
    simp

theorem degree_pos {e : Edge} (he : e∈usedEdges t) : 0<degree t e := by
  classical
  obtain ⟨a,_,ha⟩ := mem_image.mp he
  exact card_pos.mpr ⟨a,mem_filter.mpr ⟨mem_univ a,ha⟩⟩

theorem used_edge_card {e : Edge} (he : e∈usedEdges t) : e.card=2 := by
  classical
  obtain ⟨a,_,rfl⟩ := mem_image.mp he
  exact edge_card (t a.1) a.2

/-- Exact counting of real triangle-side incidences. The only geometric
hypothesis is pairwise disjointness of the actual triangular interiors. -/
theorem exact_incidence
    (hd : Pairwise (fun a b => Disjoint (t a).interior (t b).interior)) :
    3*Fintype.card α=(usedEdges t).card+(sharedEdges t).card := by
  classical
  have hc : 3*Fintype.card α=∑ e∈usedEdges t, degree t e := by
    simpa only [usedEdges,degree,card_univ,Fintype.card_prod,Fintype.card_fin,Nat.mul_comm]
      using card_eq_sum_card_image (sideMap t) (univ : Finset (α × Fin 3))
  rw [hc]
  calc
    (∑ e∈usedEdges t, degree t e)=
        ∑ e∈usedEdges t, (1+(if degree t e=2 then 1 else 0)) := by
      apply sum_congr rfl
      intro e he
      have hp := degree_pos t he
      have hu := degree_le_two t hd e
      split_ifs <;> omega
    _=(usedEdges t).card+(sharedEdges t).card := by
      simp [sum_add_distrib,sharedEdges,sum_boole]

/-- Add unused edges from any finite geometric edge universe containing the
triangle sides. Its total cardinality is left explicit for later extraction. -/
theorem exact_incidence_with_unused
    (hd : Pairwise (fun a b => Disjoint (t a).interior (t b).interior))
    (E : Finset Edge) (hE : usedEdges t⊆E) :
    3*Fintype.card α+(E\usedEdges t).card=E.card+(sharedEdges t).card := by
  have hi := exact_incidence t hd
  have he := card_sdiff_add_card_eq_card hE
  omega

end Counting

/-- Direct application to any finite injective family of actual certified
arrangement triangles. Pairwise disjointness is obtained from the certificate
predicate; it is not an additional premise of this result. -/
theorem certificate_incidence {α : Type*} [Fintype α]
    (n : ℕ) (L : ℕ → Line ℝ) (hL : NoParallel n L)
    (tri : α → Triple) (hi : Function.Injective tri)
    (ht : ∀ a, TrianglePredicate n L (tri a)) :
    let geometry := fun a => ofPredicate n L (tri a) hL (ht a)
    3*Fintype.card α=(usedEdges geometry).card+(sharedEdges geometry).card := by
  apply exact_incidence
  intro a b hab
  apply distinct_interiors_disjoint n L _ _ hL (ht a) (ht b)
  exact fun he => hab (hi he)

#print axioms edge_injective
#print axioms degree_le_two
#print axioms exact_incidence
#print axioms exact_incidence_with_unused
#print axioms certificate_incidence
end Kobon.UpperTriangleIncidence

